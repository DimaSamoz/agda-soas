from string import Template
import sys
import os
from os import path
from pathlib import Path, PurePath
from collections import OrderedDict
from gen.type import *
from gen.term import *

class Syntax:
    """Second-order syntax, consisting of a first-order type signature and second-order term signature.
    """

    def __init__(self, syn_name, ty_sig, term_sig):
        self.syn_name = syn_name
        self.ty_sig = ty_sig
        self.term_sig = term_sig
        self.term_sig.extract_type_vars(ty_sig.symbols)
        self.term_sig.all_ty_vars()
        self.term_sig.ty_name = ty_sig.name

    def render_agda(self):
        """Render the Agda files for the signature.
        """
        temp_strings = {
            'syn_name': self.syn_name,
            'type': self.ty_sig.name,
            'type_fixity': '\n' + '\n'.join(self.ty_sig.render_fixity()) + '\n',
            'type_decl': '\n  '.join(self.ty_sig.render_ty_decl()),
            'ty_vars': ' '.join(self.term_sig.ty_vars),
            'fst_ty_var': self.term_sig.ty_vars[0],
            'operator_decl': '\n  '.join(self.term_sig.render_op_symbols()),
            'sig_string' : self.__str__(),
            'sig': self.term_sig.name,
            'sig_decl': '\n  ; '.join(self.term_sig.render_tm_sig()),
            'syn_constructors': '\n    '.join([op.render_op_ctor(self.term_sig.name) for op in self.term_sig.ops]),
            'op_fixity': '\n  '.join(self.term_sig.render_op_fixity()),
            'alg_patterns': "\n      ".join([op.render_alg_pat() for op in self.term_sig.ops]),
            'sem_patterns': "\n    𝕤𝕖𝕞 ".join([op.render_sem_pat() for op in self.term_sig.ops]),
            'alg_hom_patterns': "\n      ⟨𝑎𝑙𝑔⟩ ".join([op.render_alg_hom_pat() for op in self.term_sig.ops]),
            'alg_unique_patterns': "\n      𝕤𝕖𝕞! ".join([op.render_alg_unique_pat() for op in self.term_sig.ops]),
        }
        result = ""

        if not path.exists(path.join('out', self.syn_name)):
            os.makedirs(path.join('out', self.syn_name))
        for tf in os.listdir(path.join('gen','templates')):
            with open(path.join('gen','templates',tf), 'r') as f:
                src = Template(f.read())
                result = src.substitute(temp_strings)
            with open(path.join('out', self.syn_name, tf), "w") as output:
                output.write(result)

    def spec(self):
        return {'TypeSignature' : self.ty_sig.spec(), 'TermSignature': self.term_sig.spec()}

    def __repr__(self):
        return str(self.spec())

    def __str__(self):
        return (f"{str(self.ty_sig)}\n\n{str(self.term_sig)}")

def combine_syntaxes(syn1: Syntax, syn2: Syntax):
    # if syn1.ty_sig == unsorted:
    #     # com_ops = syn2.ty_sig.ops
    #     com_ty_sig = TypeSignature(syn2.ty_sig.name, *syn2.ty_sig.ops)
    # el
    if syn2.ty_sig == unsorted:
        # com_ops = syn1.ty_sig.ops
        com_ty_sig = TypeSignature(syn1.ty_sig.name, *syn1.ty_sig.ops)

    else:
        com_ops = OrderedDict.fromkeys(syn1.ty_sig.ops + syn2.ty_sig.ops)
        com_ty_sig = TypeSignature(syn2.ty_sig.name, *com_ops)
    com_term_ops = OrderedDict.fromkeys(syn1.term_sig.ops + syn2.term_sig.ops)
    return Syntax(syn2.syn_name,
    com_ty_sig,
    TermSignature(syn2.term_sig.name, *com_term_ops))


def op(op_desc, sym=None, infix=None):
    name, *ty = op_desc.split(":")
    *arg_tys, ret_ty = ty[0].split("->")
    if arg_tys:
        arg_tys = arg_tys[0].strip().split("  ")
        if "" in arg_tys:
            arg_tys = list(filter(lambda a: a != '', arg_tys))
    return Op(name.strip(), *[at.strip() for at in arg_tys], sort=ret_ty.strip(), sym=sym, infix=infix)

def read_syntax(file):
    ops = []
    tm_cons = []
    ls = []
    path = Path(file)
    dirname = path.parent
    with open(file, 'r') as fp:
        ls = [l for l in fp.read().splitlines() if l and not l.startswith('--')]
    header = ls[0].split()
    is_ext = len(header) > 2
    syn_name = header[1]
    split_pos = ls.index(next(l for l in ls if l.startswith('term')))
    ty_sig_lines = ls[1:split_pos]
    tmsig_lines = ls[split_pos:]

    for tmcon in tmsig_lines[1:]:
        if '|' in tmcon:
            sig, props = splitstrip(tmcon, '|')
            sym, *fix = props.split()
            fix = fix[0] if fix else None
        else:
            sig = tmcon
            sym, fix = None, None
        tm_cons.append(op(sig, sym, fix))


    if ty_sig_lines:
        for ty_op in ty_sig_lines[1:]:
            nm, sig = splitstrip(ty_op, ':')
            if '|' in sig:
                ar, fix = splitstrip(sig, '|')
                ar = int(ar[0])
            else:
                ar, fix = int(sig[0]), None
            ops.append(TyOp(nm, ar, fix))

    if is_ext:
        base_file = header[3]
        base_syn = read_syntax(PurePath(dirname,base_file))
        if tmsig_lines[0].strip() == 'term':
            tm_name = base_syn.term_sig.sig_name
        else:
            tm_name = tmsig_lines[0].split()[1]
        if ty_sig_lines:
            if ty_sig_lines[0].strip() == 'type':
                ty_sig = TypeSignature(base_syn.ty_sig.name, *ops)
            else:
                ty_sig = TypeSignature(ty_sig_lines[0].split()[1], *ops)
        else:
            ty_sig = unsorted
        return combine_syntaxes(base_syn, Syntax(syn_name, ty_sig, TermSignature(tm_name, *tm_cons)))
    else:
        if ty_sig_lines:
            ty_sig = TypeSignature(ty_sig_lines[0].split()[1], *ops)
        else:
            ty_sig = unsorted
        return Syntax(syn_name, ty_sig, TermSignature(tmsig_lines[0].split()[1], *tm_cons))




if __name__ == "__main__":
    if len(sys.argv) == 2:
        syntax = read_syntax(sys.argv[1])
    syntax.render_agda()
    print(syntax.syn_name + " syntax generated successfully.")

