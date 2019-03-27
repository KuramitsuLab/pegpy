import pegpy.origami.typesys as ts
from pegpy.origami.expression import Expression
from functools import reduce

## TypeSystem

class TypeSystem(ts.Origami):
    def __init__(self, out):
        super().__init__(out)

    def Source(self, env, expr, ty):
        env.ext = Nico()
        if str(expr[4][-1][0]) == '#AssumeDecls':
            self.typeAt(env, expr[4], -1, ts.Origami.VoidType)
        for n in range(1, len(expr)):
            self.typeAt(env, expr, n, ts.Origami.VoidType)
        user = Expression.new('#TypeDecls', *env.ext.decls)
        user.context = 'user'
        expr.data.append(user)
        return expr.setType(ty)

    def Block(self, env, expr, ty):
        for n in range(1, len(expr)):
            self.typeAt(env, expr, n, ty)
        return expr.setType(ty)

    def Import(self, env, expr, ty):
        if isinstance(expr.data, str):
            expr.data = [Expression.new2('#NoImport', '')]
        else:
            for n in range(1, len(expr)):
                self.typeAt(env, expr, n, ty)
        return expr.setType(ty)

    def ImportDecl(self, env, expr, ty):
        env.ext.imp.append({'fname': bytefmt(str(expr[1][1][1])), 'sname': str(expr[1][2]), 'path': str(expr[2]), 'address': str(expr[3])})
        return expr.setType(ty)

    def Title(self, env, expr, ty):
        return expr.setType(ty)

    def VariableDecl(self, env, expr, ty):
        for n in range(1, len(expr)):
            self.typeAt(env, expr, n, None)
        for imp in env.ext.imp:
            fname = Expression.new2('#Text', imp['fname'], 'fname')
            sname = Expression.new2('#Text', imp['sname'], 'sname')
            address = Expression.new2('#Text', imp['address'], 'address')
            expr.data.append(Expression.new('#ImportPair', fname, sname, address))
        return expr.setType(ty)

    def VPair(self, env, expr, ty):
        name = str(expr[2])
        ty = env.inferName(name)
        if ty is None:
            return expr.err('untyped ' + name)
        expr[2].setType(ty)
        # expr.data.append(ty)
        return expr.setType(ty)

    def FunctionDecl(self, env, expr, ty):
        name = expr[1]
        param = Expression.new('#FDParam', *[e[1] for e in expr[2][1:] if str(e[0]) == '#FunctionParam'])
        body = Expression.new('#FDBody', *[e for e in expr[2][1:] if str(e[0]) != '#FunctionParam'])
        param.context = 'param'
        body.context = 'body'

        self.asType(env, name, ty)
        self.asType(env, param, None)

        if len(env.ext.requires) != 0:
            requires = []
            for r in env.ext.requires:
                requires.append(Expression.new('#Require', Expression.new('#Infix', r, self.asType(env, Expression('#NameExpr', 'NOT='), None), Expression.new2('#Text', 'address(0)'))))
            body.data = requires + body.data

        env.ext.requires.clear()
        self.asType(env, body, None)

        expr.data = expr.data[:-1] + [param, body]
        env.addName(str(name), Expression.ofFuncType(*param.ty.data if len(param) > 1 else ty, body.ty))

        if body.ty is not ts.Origami.VoidType:
            ret = Expression.new2('#ReturnType', body.ty, 'returns')
            expr.data.append(ret)
        if len(name) != 3 or str(name[2]) != 'constructor':
            nconst = Expression.new2('#NotConstructor', '', 'nconst')
            expr.data.append(nconst)
            if reduce(lambda x, y: x and (str(y[0]) != '#RecordStatement'), body[1:], True):
                view = Expression.new2('#ViewType', '', 'view')
                expr.data.append(view)
        if str(body[-1][0]) == '#EventStatement':
            expr = Expression.new('#EventDecl', name, param)
            return self.asType(env, expr, ty)

        return expr.setType(ty)

    def FunctionName(self, env, expr, ty):
        if len(expr) == 3:
            env.ext.funcname[str(expr[1])] = str(expr[2])
        return expr.setType(ty)

    def FDParam(self, env, expr, ty):
        for n in range(1, len(expr)):
            self.typeAt(env, expr, n, ty)
        return expr.setType(Expression.ofFuncType(*list(map(lambda e: e.ty, expr[1:]))))

    def FDPair(self, env, expr, ty):
        name = str(expr[-1])
        ty = env.inferName(name)
        if ty is None:
            return expr.err('untyped ' + name)
        expr[-1].setType(ty)
        if str(ty) in ['string']:
            memory = Expression.new2('#MemoryType', '', 'memory')
            expr.data.append(memory)
        if str(ty) in ['address']:
            env.ext.requires.append(expr[-1])
        return expr.setType(ty)

    def FDBody(self, env, expr, ty):
        for n in range(1, len(expr)):
            self.typeAt(env, expr, n, None)
        if expr[-1] in ['#Return', '#CompleteStatement']:
            return expr.setType(expr[-1].ty)
        return expr.setType(ts.Origami.VoidType)

    def Assign(self, env, expr, ty):
        self.typeAt(env, expr, 1, None)
        self.typeAt(env, expr, 2, expr[1].ty)
        return expr.setType(ts.Origami.VoidType)

    def Return(self, env, expr, ty):
        self.typeAt(env, expr, 1, ty)
        if expr[1].ty is None and isinstance(expr[1].data, str):
            type = env.inferName(expr[1].data)
            if type is not None:
                return expr.setType(type)
            return expr.err('untyped ' + expr[1].data)
        return expr.setType(expr[1].ty)

    def RecordStatement(self, env, expr, ty):
        self.typeAt(env, expr, 1, ty)
        if str(expr[2]) in env.ext.funcname:
            expr.data.append(Expression.new2('#Text', env.ext.funcname[str(expr[2])], 'name'))
        return expr.setType(ts.Origami.VoidType)

    def CompleteStatement(self, env, expr, ty):
        return expr.setType(Expression.ofType('bool'))

    def Pair(self, env, expr, ty):
        name = str(expr[2])
        ty = env.inferName(name)
        if ty is None:
            return expr.err('untyped ' + name)
        expr[2].setType(ty)
        return expr.setType(ty)

    def Map1(self, env, expr, ty):
        self.typeAt(env, expr, 2, None)
        paramty, retty = expr[2].ty[1:]
        self.typeAt(env, expr, 1, None)
        return expr.setType(retty)

    def Map2(self, env, expr, ty):
        self.typeAt(env, expr, 3, None)
        index1ty, index2ty, retty = expr[3].ty[1:]
        self.typeAt(env, expr, 1, None)
        self.typeAt(env, expr, 2, None)
        return expr.setType(retty)

    def Raw(self, env, expr, ty):
        name = str(expr)
        ty = env.inferName(name)
        return expr.setType(ty)

    def StructDefine(self, env, expr, ty):
        for n in range(2, len(expr)):
            self.typeAt(env, expr, n, ty)
        env.addName(str(expr[1]), expr[2:])
        env.ext.decls.append(expr)
        return expr.setType(ty)

    def EnumType(self, env, expr, ty):
        for n in range(1, len(expr)):
            self.typeAt(env, expr, n, ty)
        name = Expression.new2('#Text', 'Enum' + str(len(env.ext.decls)), 'name')
        env.ext.decls.append(Expression.new('#EnumDefine', Expression.new2('#EnumElement', expr[1:], 'data'), name))
        expr.data.append(name)
        return expr.setType(ty)

    def IntExpr(self, env, expr, ty):
        return expr.setType('int256')

    def WordDefine(self, env, expr, ty):
        for n in range(1, len(expr)):
            self.typeAt(env, expr, n, ty)
        return expr.done()

    def AssumeDecls(self, env, expr, ty):
        for n in range(1, len(expr)):
            self.typeAt(env, expr, n, ty)
        return expr.done()

    def AssumeDecl(self, env, expr, ty):
        for n in range(1, len(expr)):
            self.typeAt(env, expr, n, ty)
        name = str(expr[1])
        if isinstance(expr[2].data, list):
            expr[2].data = list(map(toint256, expr[2].data))
        else:
            toint256(expr[2])
        env.addName(name, expr[2])
        return expr.setType(ts.Origami.VoidType)

def bytefmt(name):
    return reduce(lambda x, y: x + format(ord(y), '04x'), name, 'v_')

def toint256(e):
    if e.data == 'int':
        e.data = 'int256'
    elif e.data == 'uint':
        e.data = 'uint256'
    return e

class Nico(object):
    __slot__ = ['imp', 'decls', 'funcname', 'requires']
    def __init__(self):
        self.imp = []
        self.decls = []
        self.funcname = {}
        self.requires = []
