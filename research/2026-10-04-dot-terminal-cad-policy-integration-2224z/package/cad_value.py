"""Structured exact CAD cell values, including multiplicity-indexed Roots.

Only closed real-algebraic observation/earlier-action inputs are executable.
The AST has no arbitrary text evaluation or source-parameter namespace.
Backend cell coverage and the full source-policy proof are separate gates.
"""
import ctypes
import re
import z3
from algebraic_history_point import decode_exact,encode_exact,PointLimit

def evaluate_value(tree,known,milliseconds=3000,max_nodes=4096,max_degree=128):
    receipts=[]
    try:
        if any(type(v) is not int or v<1 for v in (milliseconds,max_nodes,max_degree)) or milliseconds>60000:
            raise ValueError('Invalid exact cell-value resource limits.')
        if not isinstance(known,dict):raise ValueError('Malformed observation scope.')
        scope={}
        for name,record in known.items():
            if not isinstance(name,str) or not re.fullmatch(r'(h[0-9]+_[0-9]+|action_root_[A-Za-z0-9_]+)',name):
                raise ValueError('Only observed coordinates and earlier own actions may be read.')
            scope[name]=decode_exact(record)
        # Iterative shape/depth preflight precedes recursive bindings.
        pending=[(tree,0)];count=0
        while pending:
            node,depth=pending.pop();count+=1
            if count>max_nodes or depth>64:raise PointLimit('Cell AST exceeds its node/depth resource ceiling.')
            if not isinstance(node,dict):raise ValueError('Cell expressions require structured AST nodes.')
            kind=node.get('kind')
            if kind in ('add','multiply','minimum','maximum'):
                if set(node)!={'kind','args'} or not isinstance(node['args'],list) or not node['args']:
                    raise ValueError('Malformed n-ary exact cell expression.')
                pending.extend((v,depth+1) for v in node['args'])
            elif kind=='divide':
                if set(node)!={'kind','numerator','denominator'}:raise ValueError('Malformed quotient AST.')
                pending.extend((node[k],depth+1) for k in ('numerator','denominator'))
            elif kind=='power':
                if set(node)!={'kind','base','exponent'} or type(node['exponent']) is not int or abs(node['exponent'])>max_degree:
                    raise PointLimit('Unsupported or resource-limited integer power AST.')
                pending.append((node['base'],depth+1))
            elif kind=='principal_power':
                if set(node)!={'kind','base','numerator','denominator'} or type(node['numerator']) is not int or type(node['denominator']) is not int or node['denominator']<2:
                    raise ValueError('Malformed principal rational power AST.')
                if max(abs(node['numerator']),node['denominator'])>max_degree:raise PointLimit('Principal power exceeds the execution resource ceiling.')
                pending.append((node['base'],depth+1))
            elif kind=='root':
                if set(node)!={'kind','coefficients','real_root_index'} or not isinstance(node['coefficients'],list) or len(node['coefficients'])<2:
                    raise ValueError('Malformed indexed polynomial Root AST.')
                if len(node['coefficients'])-1>max_degree:raise PointLimit('Root degree exceeds this execution resource ceiling.')
                if type(node['real_root_index']) is not int or node['real_root_index']<1:raise ValueError('Invalid Root index.')
                pending.extend((v,depth+1) for v in node['coefficients'])
            elif kind=='observation':
                if set(node)!={'kind','name'} or not isinstance(node['name'],str) or node['name'] not in scope:
                    raise ValueError('Unknown/hidden/future cell coordinate.')
            elif kind=='rational':
                if set(node)!={'kind','value'}:raise ValueError('Malformed exact rational AST.')
                decode_exact(node)
            else:raise ValueError('Unsupported cell AST head.')
        def compare(a,b,op):
            value=z3.simplify(op(a,b))
            if z3.is_true(value):return True
            if z3.is_false(value):return False
            raise ValueError('A cell comparison did not reduce to a closed exact sign.')
        def roots(coeff,index):
            if compare(coeff[-1],z3.RealVal(0),lambda a,b:a==b):
                raise ValueError('Leading-coefficient zero stratum needs its own exported polynomial cell.')
            x=z3.FreshReal('indexedCADRoot')
            def polynomial(cs,v):return sum(c*(z3.RealVal(1) if i==0 else v**i) for i,c in enumerate(cs))
            solver=z3.SolverFor('QF_NRA');solver.set(timeout=milliseconds);solver.add(polynomial(coeff,x)==0)
            found=[]
            while True:
                result=solver.check()
                receipts.append({'kind':'enumerate_distinct_real_roots','status':str(result),'query_smt2':solver.to_smt2()})
                if result==z3.unknown:raise PointLimit('Root enumeration remained UNKNOWN: '+solver.reason_unknown())
                if result==z3.unsat:break
                root=z3.simplify(solver.model().eval(x,model_completion=True));root=decode_exact(encode_exact(root))
                found.append(root)
                if len(found)>len(coeff)-1:raise ValueError('Root enumeration exceeded polynomial degree.')
                solver.add(x!=root)
            ordered=[]
            for root in found:
                pos=next((i for i,v in enumerate(ordered) if compare(root,v,lambda a,b:a<b)),len(ordered))
                ordered.insert(pos,root)
            weighted=[]
            for root in ordered:
                derivative=coeff[:];multiplicity=0
                # Wolfram Root indexes real roots WITH multiplicity. The
                # minimal polynomial used in the emitted number codec has a
                # separate index; confusing these two indexes is unsound.
                while derivative and compare(polynomial(derivative,root),z3.RealVal(0),lambda a,b:a==b):
                    multiplicity+=1
                    derivative=[z3.simplify(i*derivative[i]) for i in range(1,len(derivative))]
                if not multiplicity:raise ValueError('Enumerated value failed the defining polynomial.')
                weighted.extend([root]*multiplicity)
            if index>len(weighted):raise ValueError('Requested Root is not a real root at this history point.')
            return weighted[index-1]
        def go(node):
            kind=node['kind']
            if kind=='rational':return decode_exact(node)
            if kind=='observation':return scope[node['name']]
            if kind=='root':return roots([go(v) for v in node['coefficients']],node['real_root_index'])
            if kind=='power':
                base=go(node['base']);exponent=node['exponent']
                if exponent<0 and compare(base,z3.RealVal(0),lambda a,b:a==b):raise ValueError('Undefined written negative power.')
                return z3.simplify(z3.RealVal(1) if exponent==0 else base**exponent)
            if kind=='principal_power':
                base=go(node['base']);p=node['numerator'];q=node['denominator']
                if compare(base,z3.RealVal(0),lambda a,b:a<b):
                    raise ValueError('Negative-base principal rational powers are outside this real cell codec.')
                if p<0 and compare(base,z3.RealVal(0),lambda a,b:a==b):raise ValueError('Undefined negative principal power at zero.')
                root=roots([-base]+[z3.RealVal(0)]*(q-1)+[z3.RealVal(1)],2 if q%2==0 else 1)
                return z3.simplify(z3.RealVal(1) if p==0 else root**p)
            if kind=='divide':
                a=go(node['numerator']);b=go(node['denominator'])
                if compare(b,z3.RealVal(0),lambda a,b:a==b):raise ValueError('Undefined written cell denominator.')
                return z3.simplify(a/b)
            values=[go(v) for v in node['args']]
            if kind=='add':return z3.simplify(sum(values))
            if kind=='multiply':
                value=z3.RealVal(1)
                for v in values:value=z3.simplify(value*v)
                return value
            best=values[0]
            for v in values[1:]:
                if compare(v,best,(lambda a,b:a<b) if kind=='minimum' else (lambda a,b:a>b)):best=v
            return best
        value=go(tree);encoding=encode_exact(value)
        if not compare(decode_exact(encoding),value,lambda a,b:a==b):raise ValueError('Cell-value encoding did not replay exactly.')
        return {'status':'EXACT_STRUCTURED_CAD_VALUE_SAME_BACKEND','encoding':encoding,'receipts':receipts,
                'root_index_semantics':'real roots ordered increasingly with input-polynomial multiplicity; output codec index is for its own defining polynomial'},value
    except (PointLimit,RecursionError,MemoryError,ctypes.ArgumentError) as error:
        return {'status':'UNKNOWN_CAD_VALUE_RESOURCE_LIMIT','reason':str(error),'receipts':receipts},None
    except (ValueError,TypeError,KeyError,AttributeError,IndexError,SyntaxError,ZeroDivisionError,OverflowError,z3.Z3Exception) as error:
        return {'status':'UNKNOWN_UNSUPPORTED_CAD_VALUE','reason':str(error),'receipts':receipts},None
