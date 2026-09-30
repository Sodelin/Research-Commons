"""Source-admitted dated fixture family; no enumeration of arbitrary networks."""
from fractions import Fraction as F
from metric_law import Network, Edge


def tree_with_bigons(n=4, left=2, cycles=1, arms=(F(1), F(2)), spine=F(3)):
    if not 2 <= left < n or cycles < 0:
        raise ValueError('Require 2<=left<n and cycles>=0')
    taxa = [chr(97+i) for i in range(n)]
    ages = {v: F(0) for v in taxa}
    edges = []
    def edge(i,p,c,rate,prob=None):
        edges.append(Edge(i,p,c,F(rate),None if prob is None else F(prob)))
    def clade(labels, prefix, top_age=F(1)):
        if len(labels)==1:
            return labels[0]
        node = prefix+str(len(labels))
        ages[node]=top_age
        below = clade(labels[:-1],prefix, top_age*F(len(labels)-2,len(labels)-1))
        edge(node+'L',node,below,1)
        edge(node+'R',node,labels[-1],1)
        return node
    c=clade(taxa[:left],'C')
    d=clade(taxa[left:],'D')
    ages['R']=F(2*cycles+3)
    edge('right','R',d,1)
    below=c
    for i in range(1,cycles+1):
        h,u=f'H{i}',f'U{i}'
        ages[h],ages[u]=F(2*i),F(2*i+1)
        edge(f'cut{i}',h,below,spine)
        edge(f'arm{i}a',u,h,arms[0],F(1,2))
        edge(f'arm{i}b',u,h,arms[1],F(1,2))
        below=u
    edge('top','R',below,spine)
    net=Network(ages,tuple(edges),F(1))
    net.validate(require_source=True)
    return net


def collapse_bigons(net, left=2, rate=F(3)):
    c='C'+str(left)
    drop={v for v in net.ages if v.startswith('H') or v.startswith('U')}
    ages={v:a for v,a in net.ages.items() if v not in drop}
    edges=[e for e in net.edges if e.parent not in drop and e.child not in drop and e.id!='top']
    edges.append(Edge('top','R',c,F(rate)))
    result=Network(ages,tuple(edges),net.root_rate)
    result.validate(require_source=True)
    return result


def root_diamond():
    """Root-containing level-two two-port core; each child port has two taxa."""
    ages={v:F(0) for v in 'abcd'} | {'C':F(1,2),'D':F(1,2),'HA':F(1),'HB':F(1),
                                    'V':F(2),'U':F(3),'R':F(4)}
    edges=[]
    def e(p,c,r=1,g=None):
        edges.append(Edge(p+'_'+c,p,c,F(r),None if g is None else F(g)))
    e('R','U',2);e('R','V',3)
    e('U','HA',1,F(1,3));e('V','HA',2,F(2,3))
    e('U','HB',3,F(2,5));e('V','HB',1,F(3,5))
    e('HA','C',2);e('HB','D',3)
    e('C','a');e('C','b');e('D','c');e('D','d')
    net=Network(ages,tuple(edges))
    net.validate(require_source=True)
    return net
