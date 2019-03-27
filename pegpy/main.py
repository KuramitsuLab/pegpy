#!/usr/local/bin/python
import sys, time, readline, subprocess, functools
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from pegpy.peg import *
from pegpy.gparser.gnez import gnez
import pegpy.utils as u
#import pegpy.gparser.cbase

def bold(s):
    return '\033[1m' + str(s) + '\033[0m'

def version():
    print(bold('PEGPY - A PEG-based Parsering Tools for Python'))

def read_inputs(a):
    path = Path(a)
    if path.exists():
        f = path.open()
        data = f.read()
        f.close()
        return data
    else:
        return a

def readlines(prompt):
    s = input(prompt)
    if s != '':
        return s
    else:
        l = []
        while True:
            prev = s
            s = input()
            l.append(s)
            if prev == '' and s == '':
                break
        return '\n'.join(l)

def init_output(opt):
    out = u.Writer(opt['output'] if 'output' in opt else None)
    return out

def load_grammar(opt, default = None):
    file = default if not 'grammar' in opt else opt['grammar']
    if file is None:
        raise CommandError(opt)
    g = Grammar(file)
    g.load(file)
    return g

def switch_generator(opt, default = 'math.tpeg'):
    file = default if not 'grammar' in opt else opt['grammar']
    if file.endswith('.gpeg'):
        return gnez
    return nez

# parse command

def parse(opt, out, conv=None):
    g = load_grammar(opt)
    parser = switch_generator(opt)(g, conv)
    inputs = opt['inputs']
    if len(inputs) == 0:   #Interactive Mode
        try:
            while True:
                s = readlines(bold('>>> '))
                out.dump(parser(s))
        except (EOFError, KeyboardInterrupt):
            pass
        return
    if len(inputs) == 1:
        out.dump(parser(read_inputs(inputs[0])))
        return
    else:
        for file in opt['inputs']:
            st = time.time()
            t = parser(read_inputs(file))
            et = time.time()
            out.println(file, (et - st) * 1000.0, "[ms]:", t.tag)
        return

def json(opt, out):
    parse(opt, out, lambda t: t.asJSON())

def example(opt, out):
    g = load_grammar(opt)
    p = {}
    test = 0
    ok = 0
    for testcase in g.examples:
        name, inputs, output = testcase
        if not name in g: continue
        if not name in p:
            p[name] = g.pgen(name)
        res = p[name](inputs)
        if output == None:
            if res == 'err':
                out.perror(res.pos3(), 'NG ' + name)
            else:
                out.println('OK', name, '=>', str(res))
        else:
            t = str(res).replace(" b'", " '")
            test += 1
            if t == output:
                out.println('OK', name, inputs)
                ok += 1
            else:
                out.println('NG', name, inputs, output, '!=', t)
    if test > 0:
        out.println('OK', ok, 'FAIL', test - ok, ok / test * 100.0, '%')

def peg(opt, out):
    g = load_grammar(opt)
    g.dump(out)

def origami(opt, out, grammar='konoha6.tpeg', ts=None):
    from pegpy.origami.typesys import transpile, transpile_init
    g = load_grammar(opt, grammar)
    if 'Snippet' in g: g = g['Snippet']
    parser = switch_generator(opt, 'tpeg')(g)
    origami_files = [f for f in opt['inputs'] if f.endswith('.origami')]
    source_files = [f for f in opt['inputs'] if not f.endswith('.origami')]
    env = transpile_init(origami_files, ts, out)
    if len(source_files) == 0:
        try:
            linenum = 1
            while True:
                s = readlines(bold('[{}]>>> '.format(linenum)))
                t = parser(s, '[{}]>>> '.format(linenum))
                linenum +=1
                out.verbose(repr(t))
                out.println(repr(transpile(env, t, out)))
        except (EOFError, KeyboardInterrupt):
            pass
        return None
    else:
        for input in source_files:
            t = parser(read_inputs(input), input)
            out.println(repr(transpile(env, t, out)))

def arare(opt, out):
    from pegpy.origami.arare import TypeSystem
    origami(opt,out,'arare.tpeg',TypeSystem)

def nico(opt, out):
    from pegpy.origami.nico import TypeSystem
    origami(opt,out,'nico3.tpeg',TypeSystem)

def nezcc(opt, out):
    pass

def bench(opt):
    pass

def test(opt, out):
    from pegpy.origami.arare import compile
    for f in opt['inputs']:
        print(f)
        print('---')
        print(compile(read_inputs(f)))


def update(opt, out):
    try:
        subprocess.check_call(['pip3', 'install', '-U', 'git+https://github.com/KuramitsuLab/pegpy.git'])
    except:
        pass

options = {
    'grammar': ['-g', '--grammar'],
    'start': ['-s', '--start'],
    'output': ['-o', '--output'],
    'extension': ['-X'],
    'option': ['-D'],
    'verbose': ['--verbose'],
}

def parse_options(argv, opt = options):
    def parse_each(a, d):
        if a[0].startswith('-'):
            if len(a) > 1:
                for key, list in opt.items():
                    for l in list:
                        if a[0] == l:
                            d[key] = a[1]
                            return a[2:]
            d['inputs'].extend(a)
            raise CommandError(d)
        else:
            d['inputs'].append(a[0])
            return a[1:]
    d  = {'inputs': []}
    while len(argv) > 0:
        argv = parse_each(argv, d)
    return d

def usage(opt):
    print("Usage: pegpy <command> options inputs")
    print("  -g | --grammar <file>      specify a grammar file")
    print("  -s | --start <NAME>        specify a starting rule")
    print("  -o | --output <file>       specify an output file")
    print("  -D                         specify an optional value")
    print()

    print("Example:")
    print("  pegpy parse -g math.tpeg <inputs>")
    print("  pegpy example -g math.tpeg <inputs>")
    print("  pegpy origami -g konoha6.tpeg python3.origami <inputs>")
    print()

    print("The most commonly used nez commands are:")
    print(" parse      run an interactive parser")
    print(" origami    source translation")
    print(" nezcc      generate a cross-language parser")
    print(" json       output tree as json file")
    print(" update     update pegpy (via pip)")

class CommandError(Exception):
    def __init__(self, opt):
        self.opt = opt

    def __str__(self):
        return 'CommandError ' + str(self.opt)

def main2(argv):
    cmd = argv[1]
    opt = parse_options(argv[2:])
    names = globals()
    if cmd in names:
        out = init_output(opt)
        names[cmd](opt, out)
        return out
    else:
        raise CommandError(opt)

def main():
    argv = sys.argv
    try:
        if len(argv) < 2: raise CommandError({})

        if functools.reduce(lambda x, y: x or y.startswith('edit'), argv[1:], False):
            from pegpy.playground.server import playground
            playground(argv, main2, parse_options)
        else:
            main2(argv)

    except CommandError as e:
        usage(e.opt)

if __name__ == "__main__":
    main()
