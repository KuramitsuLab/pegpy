#!/usr/local/bin/python
from pathlib import Path
import functools
import subprocess
# import readline
import time
import sys
import os
import importlib
# m = importlib.import_module('foo.some')  # -> 'module'
import pegpy


istty = True


def bold(s):
    return '\033[1m' + str(s) + '\033[0m' if istty else str(s)


COLOR = {
    "Black": '0;30', "DarkGray": '1;30',
    "Red": '0;31', "LightRed": '1;31',
    "Green": '0;32', "LightGreen": '1;32',
    "Orange": '0;33', "Yellow": '1;33',
    "Blue": '0;34', "LightBlue": '1;34',
    "Purple": '0;35', "LightPurple": '1;35',
    "Cyan": '0;36', "LightCyan": '1;36',
    "LightGray": '0;37', "White": '1;37',
}


def color(c, s):
    return '\033[{}m{}\033[0m'.format(COLOR[c], str(s)) + '' if istty else str(s)


def showing(pos, msg):
    if pos is None:
        print(msg)
    else:
        print(pos.showing(msg))


def log(type, pos, *msg):
    msg = ' '.join(map(str, msg))
    if type.startswith('err'):
        showing(pos, color('Red', '[error] ') + str(msg))
    elif type.startswith('warn'):
        showing(pos, color('Orange', '[warning] ') + str(msg))
    elif type.startswith('info') or type.startswith('notice'):
        showing(pos, color('Cyan', '[info] ') + str(msg))
    else:
        showing(pos, str(msg))


def version():
    print(bold('PEGPY - TPEG Parsing for Python3'))


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


def parse_options(argv):
    options = {
        'grammar': ['-g', '--grammar'],
        'start': ['-s', '--start'],
        'parser': ['-p', '--parser'],
        'output': ['-o', '--output'],
        'verbose': ['--verbose'],
    }

    def parse_each(a, d):
        if a[0].startswith('-'):
            if len(a) > 1:
                for key, list in options.items():
                    for l in list:
                        if a[0] == l:
                            d[key] = a[1]
                            return a[2:]
            d['inputs'].append(a)
            raise CommandUsageError
        else:
            d['inputs'].append(a[0])
            return a[1:]

    d = {'inputs': []}
    while len(argv) > 0:
        argv = parse_each(argv, d)
    d['logger'] = log
    return d


class CommandUsageError(Exception):
    pass


def usage():
    print("Usage: pegpy <command> options inputs")
    print("  -g | --grammar <file>      specify a grammar file")
    print("  -s | --start <NAME>        specify a starting rule")
    print("  -o | --output <file>       specify an output file")
    print("  -D                         specify an optional value")
    print()

    print("Example:")
    print("  pegpy parse -g math.tpeg <inputs>")
    print("  pegpy example -g math.tpeg <inputs>")
    print("  pegpy function -g math.tpeg parser.ts")
    print()

    print("The most commonly used nez commands are:")
    print(" parse      run an interactive parser")
    print(" function   generate a parser combinator function")
    print(" example    test all examples")
    print(" update     update pegpy (via pip)")


def load_grammar(options, default=None):
    file = options.get('grammar', default)
    if file is None:
        raise CommandUsageError()
    if file == 'stdin.tpeg':
        data = sys.stdin.read()
        options['basepath'] = file
        return pegpy.grammar(data, **options)
    return pegpy.grammar(file, **options)


def generator(options):
    if 'parser' in options:
        m = importlib.import_module(options['parser'])
        return m.generate
    return pegpy.generate


# parse command


def parse(options, conv=None):
    peg = load_grammar(options)
    parser = generator(options)(peg, **options)
    inputs = options['inputs']
    if len(inputs) == 0:  # Interactive Mode
        try:
            while True:
                s = readlines(bold('>>> '))
                parser(s).dump(tag=lambda x: color('Blue', x))
        except (EOFError, KeyboardInterrupt):
            pass
    elif len(inputs) == 1:
        parser(read_inputs(inputs[0])).dump(tag=lambda x: color('Blue', x))
    else:
        for file in options['inputs']:
            st = time.time()
            t = parser(read_inputs(file))
            et = time.time()
            print(file, (et - st) * 1000.0, "[ms]:", t.tag)


def dump(t, indent='  ', edge=''):
    tag = color('Blue', '#' + t.tag)
    if t.child is None:
        s = t.inputs[t.spos: t.epos]
        print(indent + edge + bold("[")+tag, color('Red', repr(s)) + bold("]"))
        return
    print(indent + edge + bold("[") + tag)
    indent2 = '  ' + indent
    for tag, child in t.subs():
        if tag != '':
            tag = tag+'='
        dump(child, indent2, tag)
    print(indent + bold("]"))


def example(options):
    peg = load_grammar(options)
    if '@@example' not in peg:
        return
    parsers = {}
    for testcase in peg['@@example']:
        name, doc = testcase
        if not name in peg:
            continue
        if not name in parsers:
            parsers[name] = generator(options)(peg, start=name)
        res = parsers[name](doc.inputs_, doc.urn_, doc.spos_, doc.epos_)
        print(bold(f'parsing {name}'))
        ok = doc.inputs_[doc.spos_:res.epos_]
        fail = doc.inputs_[res.epos_:doc.epos_]
        print(color('Green', f'{ok}')+color('Red', f'{fail}'), bold('=>'))
        res.dump()


def test(options):
    peg = load_grammar(options)
    parsers = {}
    test = 0
    ok = 0
    for testcase in peg['@@example']:
        name, pos4 = testcase
        if not name in peg:
            continue
        if not name in parsers:
            parsers[name] = generator(options)(peg, start=name)
        res = parsers[name](pos4.inputs, pos4.urn, pos4.spos, pos4.epos)
        if res == 'err':
            log('error', res, name)
        else:
            print(color('Green', f'OK {name}'), f' => {repr(res)}')
    if test > 0:
        print(color('Green', f'OK {ok}'), color(
            'Red', f'FAIL {test - ok}'), ok / test * 100.0, '%')


def peg(options):
    peg = load_grammar(options)
    print(peg)


def function(options):
    from pegpy.nezcc import nezcc
    inputs = options['inputs']
    file = 'pegpy.json' if len(inputs) == 0 else f[0]
    peg = load_grammar(options)
    nezcc(inputs[0], peg, **options)


'''
def json(opt, out):
    parse(opt, out, lambda t: t.asJSON())

def nezcc(opt, out):
    pass


def bench(opt):
    pass
'''


def update(options):
    try:
        # pip3 install -U git+https://github.com/KuramitsuLab/pegpy.git
        subprocess.check_call(
            ['pip3', 'install', '-U', 'git+https://github.com/KuramitsuLab/pegpy.git'])
    except:
        pass


def beta(options):
    try:
        # pip3 install -U git+https://github.com/KuramitsuLab/pegpy.git
        subprocess.check_call(
            ['pip3', 'install', '-U', 'git+https://github.com/KuramitsuLab/pegpy.git'])
    except:
        pass


def main(argv=sys.argv):
    try:
        names = globals()
        if len(argv) > 1:
            cmd = argv[1]
            options = parse_options(argv[2:])
            if cmd in names:
                names[cmd](options)
                return
        raise CommandUsageError()
    except CommandUsageError:
        usage()


if __name__ == "__main__":
    main(sys.argv)
