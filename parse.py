text = r'''
loop=0
end=0
integers={-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7}
univ={-1, -2, -3, -4, -5, -6, -7, -8, 0, 1, 2, 3, 4, 5, 6, 7, AbstractClass$0, AbstractClass$1, AbstractMethod$0, AbstractName$0, AbstractName$1, Call$0, ConcreteMethod$0, ConcreteMethod$1, MethodName$0, MethodName$1, StaticKeyword$0, UseStaticAttribute$0, Var$0, Var$1}
Int={-1, -2, -3, -4, -5, -6, -7, -8, 0, 1, 2, 3, 4, 5, 6, 7}
seq/Int={0, 1, 2, 3}
String={}
none={}
this/Class={AbstractClass$0, AbstractClass$1}
this/Class<:methods={AbstractClass$0->AbstractMethod$0, AbstractClass$0->ConcreteMethod$1, AbstractClass$1->ConcreteMethod$0}
this/Class<:parent={AbstractClass$0->AbstractClass$1}
this/AbstractClass={AbstractClass$0, AbstractClass$1}
this/ConcreteClass={}
this/MethodName={MethodName$0, MethodName$1}
this/Method={AbstractMethod$0, ConcreteMethod$0, ConcreteMethod$1}
this/Method<:method_name={AbstractMethod$0->MethodName$0, ConcreteMethod$0->MethodName$1, ConcreteMethod$1->MethodName$1}
this/ConcreteMethod={ConcreteMethod$0, ConcreteMethod$1}
this/ConcreteMethod<:calls={ConcreteMethod$0->Call$0}
this/ConcreteMethod<:use_static_attribute={ConcreteMethod$1->UseStaticAttribute$0}
this/AbstractMethod={AbstractMethod$0}
this/Call={Call$0}
this/Call<:receiver={Call$0->Var$1}
this/Call<:call_method_name={Call$0->MethodName$0}
this/Call<:resolves_to={Call$0->AbstractMethod$0}
this/Type={AbstractName$0, AbstractName$1}
this/Type<:supertypes={AbstractName$1->AbstractName$0}
this/Type<:names_class={AbstractName$0->AbstractClass$1, AbstractName$1->AbstractClass$0}
this/AbstractName={AbstractName$0, AbstractName$1}
this/ConcreteName={}
this/Receiver={StaticKeyword$0, Var$0, Var$1}
this/StaticKeyword={StaticKeyword$0}
this/Var={Var$0, Var$1}
this/Var<:var_ty={Var$0->AbstractName$1, Var$1->AbstractName$0}
this/Var<:var_points_to={Var$0->AbstractClass$0, Var$1->Var$0}
this/UseStaticAttribute={UseStaticAttribute$0}
skolem $c={AbstractMethod$0->AbstractClass$0, ConcreteMethod$0->AbstractClass$1, ConcreteMethod$1->AbstractClass$0}
skolem $m={MethodName$0->AbstractMethod$0, MethodName$1->ConcreteMethod$1}
skolem $call={Call$0}
'''

from collections import defaultdict

def parse_facts(text):
    facts = defaultdict(dict)
    for line in text.split('\n'):
        if not line.startswith('this/'):
            continue
        lhs, raw_rhs = line[len('this/'):].split('=')
        rhs = raw_rhs[1:-1].split(', ')  # strip surrounding braces and parse list
        if '<:' not in lhs:
            sig = lhs
            for name in rhs:
                facts[sig][name] = {}
        else:
            sig, prop = lhs.split('<:')
            for mapping in rhs:
                if mapping:
                    name, val = mapping.split('->')
                    if prop not in facts[sig][name]:
                        facts[sig][name][prop] = []
                    facts[sig][name][prop].append(val)

    return facts


def facts_to_code(facts):
    lines = []
    for class_name, class_ in reversed(facts['Class'].items()):
        extends_str = ''
        parent_methods = []
        if 'parent' in class_:
            parent_id = class_['parent'][0]
            parent = facts['Class'][parent_id]
            if 'methods' in parent:
                parent_methods = parent['methods']
            extends_str = f' extends {parent_id}'
        if class_name in facts['AbstractClass']:
            abstract_str = 'abstract '
        else:
            abstract_str = ''
        lines.append(f'{abstract_str}class {class_name}{extends_str}')
        if 'methods' in class_:
            for method_id in class_['methods']:
                if method_id in parent_methods:
                    continue
                method = facts['Method'][method_id]
                method_name = method['method_name'][0]
                if method_id in facts['AbstractMethod']:
                    lines.append(f'  abstract def {method_name}')
                else:
                    lines.append(f'  def {method_name}     # {method_id}')
                if method_id in facts['ConcreteMethod']:
                    concrete_method = facts['ConcreteMethod'][method_id]
                    if 'calls' in concrete_method:
                        for call_id in concrete_method['calls']:
                            call = facts['Call'][call_id]
                            receiver = call['receiver'][0]
                            method_name = call['call_method_name'][0]
                            comment = 'resolves to ' + ', '.join(call['resolves_to'])
                            lines.append(f'    {receiver}.{method_name}()     # {comment}')
        lines.append('\n')
    for var_id, var in facts['Var'].items():
        var_ty_id = var['var_ty'][0]
        names_class = facts['Type'][var_ty_id]['names_class'][0]
        if var_ty_id in facts['AbstractName']:
            ty_str = f'classname<{names_class}>'
        elif var_ty_id in facts['ConcreteName']:
            ty_str = f'classname<{names_class}>'
        else:
            raise Exception(f'could not find type {var_ty_id}')
        points_to = var['var_points_to'][0]
        lines.append(f'{var_id} : {ty_str} = {points_to}')



    return '\n'.join(lines)


def main():
    facts = parse_facts(text)
    print('\n')
    print(facts_to_code(facts))
    print('\n')

if __name__ == '__main__':
    main()

