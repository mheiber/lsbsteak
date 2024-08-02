import os
from pathlib import Path

with open(Path(os.environ['HOME']) / 'out.txt') as f:
    text = f.read()


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
                    lines.append(f'  abstract static function {method_name}()   // {method_id}')
                if method_id in facts['ConcreteMethod']:
                    concrete_method = facts['ConcreteMethod'][method_id]
                    if 'use_static_attribute' in concrete_method:
                        if len(concrete_method['use_static_attribute']):
                            lines.append('  <<__UseStatic>>')
                    lines.append(f'  static function {method_name}()            // {method_id}')
                    if 'calls' in concrete_method:
                        for call_id in concrete_method['calls']:
                            call = facts['Call'][call_id]
                            receiver = call['receiver'][0]
                            if receiver == 'StaticKeyword$0':
                                receiver = 'static'
                            method_name = call['call_method_name'][0]
                            resolves_to = 'resolves to ' + ', '.join(call['resolves_to'])
                            lines.append(f'    {receiver}::{method_name}()     // {call_id} {resolves_to}')
        lines.append('\n')
    for var_id, var in facts['Var'].items():
        if 'var_ty' in var:
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

