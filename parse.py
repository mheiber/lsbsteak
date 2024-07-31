
text = r'''
loop=0
end=0
integers={-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7}
univ={-1, -2, -3, -4, -5, -6, -7, -8, 0, 1, 2, 3, 4, 5, 6, 7, AbstractClass$0, AbstractType$0, Call$0, ConcreteMethod$0, ConcreteMethod$1, LsbAttribute$0, MethodName$0, MethodName$1, StaticKeyword$0, Var$0, Var$1}
Int={-1, -2, -3, -4, -5, -6, -7, -8, 0, 1, 2, 3, 4, 5, 6, 7}
seq/Int={0, 1, 2}
String={}
none={}
this/Class={AbstractClass$0}
this/Class<:methods={AbstractClass$0->ConcreteMethod$0, AbstractClass$0->ConcreteMethod$1}
this/Class<:parent={}
this/AbstractClass={AbstractClass$0}
this/ConcreteClass={}
this/MethodName={MethodName$0, MethodName$1}
this/Method={ConcreteMethod$0, ConcreteMethod$1}
this/Method<:method_name={ConcreteMethod$0->MethodName$1, ConcreteMethod$1->MethodName$0}
this/ConcreteMethod={ConcreteMethod$0, ConcreteMethod$1}
this/ConcreteMethod<:calls={ConcreteMethod$1->Call$0}
this/ConcreteMethod<:lsbAttribute={ConcreteMethod$0->LsbAttribute$0, ConcreteMethod$1->LsbAttribute$0}
this/AbstractMethod={}
this/Call={Call$0}
this/Call<:receiver={Call$0->StaticKeyword$0}
this/Call<:call_method_name={Call$0->MethodName$0}
this/Call<:resolves_to={Call$0->ConcreteMethod$1}
this/Type={AbstractType$0}
this/Type<:supertypes={AbstractType$0->AbstractType$0}
this/Type<:names_class={AbstractType$0->AbstractClass$0}
this/AbstractType={AbstractType$0}
this/ConcreteType={}
this/Receiver={StaticKeyword$0, Var$0, Var$1}
this/StaticKeyword={StaticKeyword$0}
this/Var={Var$0, Var$1}
this/Var<:var_ty={Var$0->AbstractType$0, Var$1->AbstractType$0}
this/Var<:var_points_to={Var$0->Var$1, Var$1->AbstractClass$0}
this/LsbAttribute={LsbAttribute$0}
skolem $show_c={ConcreteMethod$0->AbstractClass$0, ConcreteMethod$1->AbstractClass$0}
skolem $show_m={Call$0->ConcreteMethod$1}
skolem $show_m'={MethodName$0->ConcreteMethod$1, MethodName$1->ConcreteMethod$0}
skolem $show_call={Call$0}
'''

text = r'''
loop=0
end=0
integers={-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7}
univ={-1, -2, -3, -4, -5, -6, -7, -8, 0, 1, 2, 3, 4, 5, 6, 7, AbstractType$0, AbstractType$1, Call$0, Call$1, ConcreteClass$0, ConcreteClass$1, ConcreteMethod$0, ConcreteMethod$1, ConcreteMethod$2, ConcreteType$0, ConcreteType$1, LsbAttribute$0, MethodName$0, MethodName$1, StaticKeyword$0, Var$0, Var$1, Var$2}
Int={-1, -2, -3, -4, -5, -6, -7, -8, 0, 1, 2, 3, 4, 5, 6, 7}
seq/Int={0, 1, 2, 3}
String={}
none={}
this/Class={ConcreteClass$0, ConcreteClass$1}
this/Class<:methods={ConcreteClass$0->ConcreteMethod$0, ConcreteClass$0->ConcreteMethod$2, ConcreteClass$1->ConcreteMethod$1, ConcreteClass$1->ConcreteMethod$2}
this/Class<:parent={ConcreteClass$1->ConcreteClass$0}
this/AbstractClass={}
this/ConcreteClass={ConcreteClass$0, ConcreteClass$1}
this/MethodName={MethodName$0, MethodName$1}
this/Method={ConcreteMethod$0, ConcreteMethod$1, ConcreteMethod$2}
this/Method<:method_name={ConcreteMethod$0->MethodName$1, ConcreteMethod$1->MethodName$1, ConcreteMethod$2->MethodName$0}
this/ConcreteMethod={ConcreteMethod$0, ConcreteMethod$1, ConcreteMethod$2}
this/ConcreteMethod<:calls={ConcreteMethod$2->Call$0, ConcreteMethod$2->Call$1}
this/ConcreteMethod<:lsbAttribute={ConcreteMethod$0->LsbAttribute$0, ConcreteMethod$1->LsbAttribute$0, ConcreteMethod$2->LsbAttribute$0}
this/AbstractMethod={}
this/Call={Call$0, Call$1}
this/Call<:receiver={Call$0->Var$2, Call$1->Var$1}
this/Call<:call_method_name={Call$0->MethodName$0, Call$1->MethodName$1}
this/Call<:resolves_to={Call$0->ConcreteMethod$2, Call$1->ConcreteMethod$1}
this/Type={AbstractType$0, AbstractType$1, ConcreteType$0, ConcreteType$1}
this/Type<:supertypes={AbstractType$1->AbstractType$0, AbstractType$1->AbstractType$1, AbstractType$1->ConcreteType$1, ConcreteType$0->AbstractType$0, ConcreteType$0->AbstractType$1, ConcreteType$0->ConcreteType$0, ConcreteType$0->ConcreteType$1, ConcreteType$1->ConcreteType$1}
this/Type<:names_class={AbstractType$0->ConcreteClass$1, AbstractType$1->ConcreteClass$1, ConcreteType$0->ConcreteClass$1, ConcreteType$1->ConcreteClass$0}
this/AbstractType={AbstractType$0, AbstractType$1}
this/ConcreteType={ConcreteType$0, ConcreteType$1}
this/Receiver={StaticKeyword$0, Var$0, Var$1, Var$2}
this/StaticKeyword={StaticKeyword$0}
this/Var={Var$0, Var$1, Var$2}
this/Var<:var_ty={Var$0->ConcreteType$0, Var$1->ConcreteType$1, Var$2->ConcreteType$1}
this/Var<:var_points_to={Var$0->ConcreteClass$1, Var$1->Var$0, Var$2->Var$1}
this/LsbAttribute={LsbAttribute$0}
skolem $show_complicated_c={ConcreteMethod$0->ConcreteClass$0, ConcreteMethod$1->ConcreteClass$1, ConcreteMethod$2->ConcreteClass$0}
skolem $show_complicated_m={Call$0->ConcreteMethod$2, Call$1->ConcreteMethod$2}
skolem $show_complicated_m'={MethodName$0->ConcreteMethod$2, MethodName$1->ConcreteMethod$0}
skolem $has_inherited_method_m={ConcreteMethod$2}
skolem $has_inherited_method_c1={ConcreteClass$1}
skolem $has_inherited_method_c2={ConcreteClass$0}
skolem $has_interesting_method_call_call={Call$1}
skolem $has_override_m={ConcreteMethod$1}
skolem $has_override_c1={ConcreteClass$1}
skolem $has_override_c2={ConcreteClass$0}

'''

from collections import defaultdict

def parse_facts(text): facts = defaultdict(dict)
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
    for class_name, class_ in facts['Class'].items():
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
        lines.append(f'{abstract_str}class {class_name}{extends_str}:')
        if 'methods' in class_:
            for method_id in class_['methods']:
                if method_id in parent_methods:
                    continue
                method = facts['Method'][method_id]
                method_name = method['method_name'][0]
                if method_id in facts['AbstractMethod']:
                    lines.append(f'  abstract def {method_name}')
                else:
                    lines.append(f'  def {method_name}:     # {method_id}')
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



    return '\n'.join(lines)


def main():
    facts = parse_facts(text)
    print(facts_to_code(facts))

if __name__ == '__main__':
    main()

