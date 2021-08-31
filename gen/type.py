"""Type operators and signatures."""

class TyOp:
  """Type operator of a sype signature.
  """

  def __init__(self, name, arity, infix=None, derived=False):
    """Initialise type operator

    Args:
        name (str): Name of a operator (can be symbol with underscores)
        arity (number): Arity of the operator
        infix (str, optional): str describing the associativity and fixity of the operator. Defaults to None.
    """
    self.name = name
    self.arity = arity
    self.padding = 0    # Padding required based on the longest type operator name
    self.derived = derived
    self.infix = None
    if infix:
        if infix[0] in ['l', 'r']:
            self.infix = (infix[0], infix[1:])
        else: self.infix = ('', infix)

  def __eq__(self, o: object) -> bool:
      return self.name == o.name

  def __hash__(self) -> int:
      return hash(self.name)

  def spec(self):
    """Specification of a type operator

    Returns:
        dict: Dictionary representing the type operator
    """

    spec = {'TyOpName': self.name, 'TyOpAr': self.arity}
    if self.infix:
        spec['TyFixity'] = self.infix
    return spec

  def __repr__(self):
    return str(self.spec())

  def __str__(self):
    return f"{self.name}{' ' * self.padding} : {self.arity}-ary" + (f" | {self.infix[0]}{self.infix[1]}" if self.infix else "")


class TypeSignature:
  """Simple type signature of a second-order syntax
  """

  def __init__(self, name, *ops: list[TyOp]):
    """Initialise type signature with type name and list of type operator lists.

    Args:
        name (str): Name of the type signature
        *ops (list[TyOp]): List of type operators
    """
    self.name = name
    self.all_ops = list(ops)

  @property
  def symbols(self):
    symbols = set()  
    max_op_len = max([len(tc.name) for tc in self.all_ops])

    for op in self.ops:
        symbols = symbols.union(set(op.name.split('_')))
        op.padding = max_op_len - len(op.name)
    symbols.discard("")
    return symbols


  @property
  def ops(self):
    return [op for op in self.all_ops if not op.derived]

  @property
  def derived_ty_ops(self):
    return [op for op in self.all_ops if op.derived]

  def render_ty_decl(self):
    """Render constructors of type declaration.

    Returns:
        list[str]: List of constructors for the type declaration
    """
    ls = []
    ls += [f"{op.name}{' ' * op.padding} : {(self.name + ' → ')*op.arity + self.name}"
        for op in self.ops]
    return ls

  def render_fixity(self):
    """Render fixity information for type operators.

    Returns:
        list[str]: Fixity declarations for the operators
    """
    ls = []
    for op in self.ops:
        if op.infix:
            assoc, infix = op.infix
            ls.append(f"infix{assoc} {infix} {op.name}")
    return ls

  def render_all(self):
    if isinstance(self, Unsorted):
      return "open import SOAS.Common"
    ls = f"-- Type declaration\ndata {self.name} : Set where\n  "

    return ls + "\n  ".join(self.render_ty_decl()) + "\n" + "\n".join(self.render_fixity()) 



  def spec(self):
    """Specification of a type signature.

    Returns:
        dict: Dictionary representing the type signature
    """
    return {'TyName' : self.name,
            'TyOps' : [tc.spec() for tc in self.ops ] }

  def __repr__(self):
    return str(self.spec())

  def __str__(self):
    ls = [f"type"]
    ls += ['  ' + str(tc) for tc in self.ops]
    return '\n'.join(ls)

# Special case of an unsorted type signature: type name '*T' and a single nullary type constructor
class Unsorted(TypeSignature):
  def __init__(self):
    return super().__init__("*T", TyOp('*', 0))
