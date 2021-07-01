import collections
dpll_calls = 0
seq_rooms_visited = []

class Expr:
    def __init__(self, op, *args):
        self.op = str(op)
        self.args = args

    def __invert__(self):
        return Expr('~', self)

    def __and__(self, rhs):
        return Expr('&', self, rhs)

    def __xor__(self, rhs):
        return Expr('^', self, rhs)

    def __or__(self, rhs):
        """Allow both P | Q, and P |'==>'| Q."""
        if isinstance(rhs, Expression):
            return Expr('|', self, rhs)
        else:
            return PartialExpr(rhs, self)

    def __eq__(self, other):
        return isinstance(other, Expr) and self.op == other.op and self.args == other.args

    def __hash__(self):
        return hash(self.op) ^ hash(self.args)

    def __repr__(self):
        op = self.op
        args = [str(arg) for arg in self.args]
        if op.isidentifier():  # f(x) or f(x, y)
            return '{}({})'.format(op, ', '.join(args)) if args else op
        elif len(args) == 1:  # -x or -(x + 1)
            return op + args[0]
        else:  # (x - y)
            opp = (' ' + op + ' ')
            return '(' + opp.join(args) + ')'


Number = (int, float, complex)
Expression = (Expr, Number)

class PartialExpr:
    def __init__(self, op, lhs):
        self.op = op
        self.lhs = lhs

    def __or__(self, rhs):
        return Expr(self.op, self.lhs, rhs)

    def __repr__(self):
        return "PartialExpr('{}', {})".format(self.op, self.lhs)

def Symbol(name):
    return Expr(name)

def symbols(names):
    return tuple(Symbol(name) for name in names.replace(',', ' ').split())

def expr(x):
    if isinstance(x, str):
        return eval(expr_handle_infix_ops(x), defaultkeydict(Symbol))
    else:
        return x

infix_ops = '==> <== <=>'.split()

def expr_handle_infix_ops(x):
    for op in infix_ops:
        x = x.replace(op, '|' + repr(op) + '|')
    return x

class defaultkeydict(collections.defaultdict):
    def __missing__(self, key):
        self[key] = result = self.default_factory(key)
        return result


def wumpus(x, y):
    return Expr('W', x, y)

def pit(x, y):
    return Expr('P', x, y)

def breeze(x, y):
    return Expr('B', x, y)

def stench(x, y):
    return Expr('S', x, y)

def implies(lhs, rhs):
    return Expr('==>', lhs, rhs)

def equiv(lhs, rhs):
    return Expr('<=>', lhs, rhs)


class WumpusKB():
    def __init__(self, dimrow):
        self.clauses = []
        self.dimrow = dimrow
        self.tell(~wumpus(1, 1))
        self.tell(~pit(1, 1))
        self.tell(~wumpus(4, 4))
        self.tell(~pit(4, 4))

        for y in range(1, dimrow + 1):
            for x in range(1, dimrow + 1):
                pits_in = list()
                wumpus_in = list()

                if x > 1:  # West room exists
                    pits_in.append(pit(x - 1, y))
                    wumpus_in.append(wumpus(x - 1, y))

                if y < dimrow:  # North room exists
                    pits_in.append(pit(x, y + 1))
                    wumpus_in.append(wumpus(x, y + 1))

                if x < dimrow:  # East room exists
                    pits_in.append(pit(x + 1, y))
                    wumpus_in.append(wumpus(x + 1, y))

                if y > 1:  # South room exists
                    pits_in.append(pit(x, y - 1))
                    wumpus_in.append(wumpus(x, y - 1))

                self.tell(equiv(breeze(x, y), new_disjunction(pits_in)))
                self.tell(equiv(stench(x, y), new_disjunction(wumpus_in)))

        # Rule that describes existence of at least one Wumpus
        wumpus_at_least = list()
        for x in range(1, dimrow + 1):
            for y in range(1, dimrow + 1):
                wumpus_at_least.append(wumpus(x, y))
        self.tell(new_disjunction(wumpus_at_least))

        # Rule that describes existence of at most one Wumpus
        for i in range(1, dimrow + 1):
            for j in range(1, dimrow + 1):
                for u in range(1, dimrow + 1):
                    for v in range(1, dimrow + 1):
                        if i != u or j != v:
                            self.tell(~wumpus(i, j) | ~wumpus(u, v))
       
        # Rule that describes existence of at least one Pit
        pits_at_least = list()
        for x in range(1, dimrow + 1):
            for y in range(1, dimrow + 1):
                pits_at_least.append(pit(x, y))
        self.tell(new_disjunction(pits_at_least))
        
        # Rule that describes existence of at most one Pit
        for i in range(1, dimrow + 1):
            for j in range(1, dimrow + 1):
                for u in range(1, dimrow + 1):
                    for v in range(1, dimrow + 1):
                        if i != u or j != v:
                            self.tell(~pit(i, j) | ~pit(u, v))

    def tell(self, sentence):
        self.clauses.extend(conjuncts(to_cnf(sentence)))
       
    def ask_if_true(self, query):
        c = conjuncts(to_cnf(query))
        c.extend(self.clauses)
        s = list(prop_symbols(query))
        for clause in self.clauses:
            s.extend(list(prop_symbols(clause)))
        s = set(s)
        symbols = list(s)
        return dpll(c, symbols, {}) is not False


def prop_symbols(x):
    if not isinstance(x, Expr):
        return set()
    elif is_prop_symbol(x.op):
        return {x}
    else:
        return {symbol for arg in x.args for symbol in prop_symbols(arg)}

def is_prop_symbol(s):
    return is_symbol(s) and s[0].isupper()

def new_disjunction(sentences):
    t = sentences[0]
    for i in range(1, len(sentences)):
        t |= sentences[i]
    return t

def conjuncts(s):
    return dissociate('&', [s])

def is_symbol(s):
    return isinstance(s, str) and s[:1].isalpha()

def dissociate(op, args):
    result = []

    def collect(subargs):
        for arg in subargs:
            if arg.op == op:
                collect(arg.args)
            else:
                result.append(arg)

    collect(args)
    return result

def to_cnf(s):
    s = expr(s)
    if isinstance(s, str):
        s = expr(s)
    s = eliminate_implications(s)  
    s = move_not_inwards(s)  
    return distribute_and_over_or(s)  


def eliminate_implications(s):
    s = expr(s)
    if not s.args or is_symbol(s.op):
        return s 
    args = list(map(eliminate_implications, s.args))
    a, b = args[0], args[-1]
    if s.op == '==>':
        return b | ~a
    elif s.op == '<==':
        return a | ~b
    elif s.op == '<=>':
        return (a | ~b) & (b | ~a)
    elif s.op == '^':
        assert len(args) == 2  
        return (a & ~b) | (~a & b)
    else:
        assert s.op in ('&', '|', '~')
        return Expr(s.op, *args)

def move_not_inwards(s):
    s = expr(s)
    if s.op == '~':
        def NOT(b):
            return move_not_inwards(~b)

        a = s.args[0]
        if a.op == '~':
            return move_not_inwards(a.args[0])
        if a.op == '&':
            return associate('|', list(map(NOT, a.args)))
        if a.op == '|':
            return associate('&', list(map(NOT, a.args)))
        return s
    elif is_symbol(s.op) or not s.args:
        return s
    else:
        return Expr(s.op, *list(map(move_not_inwards, s.args)))

def distribute_and_over_or(s):
    s = expr(s)
    if s.op == '|':
        s = associate('|', s.args)
        if s.op != '|':
            return distribute_and_over_or(s)
        if len(s.args) == 0:
            return False
        if len(s.args) == 1:
            return distribute_and_over_or(s.args[0])
        conj = first(arg for arg in s.args if arg.op == '&')
        if not conj:
            return s
        others = [a for a in s.args if a is not conj]
        rest = associate('|', others)
        return associate('&', [distribute_and_over_or(c | rest) for c in conj.args])
    elif s.op == '&':
        return associate('&', list(map(distribute_and_over_or, s.args)))
    else:
        return s


def first(iterable, default=None):
    return next(iter(iterable), default)

def associate(op, args):
    args = dissociate(op, args)
    if len(args) == 0:
        return _op_identity[op]
    elif len(args) == 1:
        return args[0]
    else:
        return Expr(op, *args)

_op_identity = {'&': True, '|': False, '+': 0, '*': 1}

def dpll(clauses, symbols, model):
    global dpll_calls
    dpll_calls += 1
    unknown_clauses = []  
    for c in clauses:
        val = pl_true(c, model)
        if val is False:
            return False
        if val is not True:
            unknown_clauses.append(c)
    if not unknown_clauses:
        return model
    P, value = find_unit_clause(clauses, model)
    if P:
        return dpll(clauses, remove_all(P, symbols), extend(model, P, value))
    P, value = find_pure_symbol(symbols, unknown_clauses)
    if P:
        return dpll(clauses, remove_all(P, symbols), extend(model, P, value))
    P, symbols = symbols[0], symbols[1:]
    return (dpll(clauses, symbols, extend(model, P, True)) or
            dpll(clauses, symbols, extend(model, P, False)))

def pl_true(exp, model={}):
    if exp in (True, False):
        return exp
    op, args = exp.op, exp.args
    if is_prop_symbol(op):
        return model.get(exp)
    elif op == '~':
        p = pl_true(args[0], model)
        if p is None:
            return None
        else:
            return not p
    elif op == '|':
        result = False
        for arg in args:
            p = pl_true(arg, model)
            if p is True:
                return True
            if p is None:
                result = None
        return result
    elif op == '&':
        result = True
        for arg in args:
            p = pl_true(arg, model)
            if p is False:
                return False
            if p is None:
                result = None
        return result
    p, q = args
    if op == '==>':
        return pl_true(~p | q, model)
    elif op == '<==':
        return pl_true(p | ~q, model)
    pt = pl_true(p, model)
    if pt is None:
        return None
    qt = pl_true(q, model)
    if qt is None:
        return None
    if op == '<=>':
        return pt == qt
    elif op == '^': 
        return pt != qt

def remove_all(item, seq):
    if isinstance(seq, str):
        return seq.replace(item, '')
    elif isinstance(seq, set):
        rest = seq.copy()
        rest.remove(item)
        return rest
    else:
        return [x for x in seq if x != item]

def extend(s, var, val):
    s2 = s.copy()
    s2[var] = val
    return s2

def find_pure_symbol(symbols, clauses):
    for s in symbols:
        found_pos, found_neg = False, False
        for c in clauses:
            if not found_pos and s in disjuncts(c):
                found_pos = True
            if not found_neg and ~s in disjuncts(c):
                found_neg = True
        if found_pos != found_neg:
            return s, found_pos
    return None, None

def disjuncts(s):
    return dissociate('|', [s])

def find_unit_clause(clauses, model):
    for clause in clauses:
        P, value = unit_clause_assign(clause, model)
        if P:
            return P, value
    return None, None

def unit_clause_assign(clause, model):
    P, value = None, None
    for literal in disjuncts(clause):
        sym, positive = inspect_literal(literal)
        if sym in model:
            if model[sym] == positive:
                return None, None 
        elif P:
            return None, None
        else:
            P, value = sym, positive
    return P, value


def inspect_literal(literal):
    if literal.op == '~':
        return literal.args[0], False
    else:
        return literal, True

class Agent:    
    def __init__(self):
        self._wumpusWorld = [
                 ['','','',''], 
                 ['','','P',''], 
                 ['','W','',''],
                 ['','','',''], 
                ] 
    
        self._curLoc = [1,1]
        self._isAlive = True
        self._hasExited = False

        self.kb = WumpusKB(4)
        self.visited = [[False for x in range(4)] for y in range(4)]
        self.action = None
        self.plan = []
        

    def _FindIndicesForLocation(self,loc):
        x,y = loc
        i,j = 4-y, x-1
        return i,j

    def _CheckForPitWumpus(self):
        ww = self._wumpusWorld
        i,j = self._FindIndicesForLocation(self._curLoc)
        if 'P' in ww[i][j] or 'W' in ww[i][j]:
            print(ww[i][j])
            self._isAlive = False
            print('Agent is DEAD.')
        return self._isAlive

    def TakeAction(self,action): # The function takes an action and returns whether the Agent is alive
                                # after taking the action.
        validActions = ['Up','Down','Left','Right']
        assert action in validActions, 'Invalid Action.'
        if self._isAlive == False:
            print('Action cannot be performed. Agent is DEAD. Location:{0}'.format(self._curLoc))
            return False
        if self._hasExited == True:
            print('Action cannot be performed. Agent has exited the Wumpus world.{0}'.format(self._curLoc))
            return False

        index = validActions.index(action)
        validMoves = [[0,1],[0,-1],[-1,0],[1,0]]
        move = validMoves[index]
        newLoc = []
        print("cur_loc: ", self._curLoc, "move: ", move)
        for v, inc in zip(self._curLoc,move):
            z = v + inc #increment location index
            z = 4 if z>4 else 1 if z<1 else z #Ensure that index is between 1 and 4
            newLoc.append(z)
        self._curLoc = newLoc
        print('Action Taken: {0}, Current Location {1}'.format(action,self._curLoc))
        if self._curLoc[0]==4 and self._curLoc[1]==4:
            self._hasExited=True
        return self._CheckForPitWumpus()
    
    def _FindAdjacentRooms(self):
        cLoc = self._curLoc
        validMoves = [[0,1],[0,-1],[-1,0],[1,0]]
        adjRooms = []
        for vM in validMoves:
            room = []
            valid = True
            for v, inc in zip(cLoc,vM):
                z = v + inc
                if z<1 or z>4:
                    valid = False
                    break
                else:
                    room.append(z)
            if valid==True:
                adjRooms.append(room)
        return adjRooms
        

    def PerceiveCurrentLocation(self): #This function perceives the current location. 
                                        #It tells whether breeze and stench are present in the current location.
        breeze, stench = False, False
        ww = self._wumpusWorld
        if self._isAlive == False:
            print('Agent cannot perceive. Agent is DEAD. Location:{0}'.format(self._curLoc))
            return [None,None]
        if self._hasExited == True:
            print('Agent cannot perceive. Agent has exited the Wumpus World.{0}'.format(self._curLoc))
            return [None,None]

        adjRooms = self._FindAdjacentRooms()
        for room in adjRooms:
            i,j = self._FindIndicesForLocation(room)
            if 'P' in ww[i][j]:
                breeze = True
            if 'W' in ww[i][j]:
                stench = True
        return [breeze,stench]
    
    def FindCurrentLocation(self):
        return self._curLoc


    def PL_Wumpus_Agent(self):
        if self._hasExited:
            return 

        seq_rooms_visited.append(self._curLoc)

        idxi, idxj = self._FindIndicesForLocation(self._curLoc)
        # Mark _curLoc as visited
        self.visited[idxi][idxj] = True
        x, y = self._curLoc
        
        # get the percept
        percept = self.PerceiveCurrentLocation()

        # tell the kb about the percept
        self.kb.tell(~wumpus(x, y))
        self.kb.tell(~pit(x,y))

        if percept[0] is True:
            self.kb.tell(breeze(x,y))
        else:
            self.kb.tell(~breeze(x,y))
        
        if percept[1] is True:
            self.kb.tell(stench(x,y))
        else:
            self.kb.tell(~stench(x,y))
        
        if len(self.plan) != 0:
            self.action = self.plan.pop(0)

        else:
            flag = True
            for i in range(1,5):
                for j in range(1,5):
                    idxi, idxj = self._FindIndicesForLocation([i, j])
                    if self.visited[idxi][idxj] is False and self.kb.ask_if_true(~wumpus(i,j) & ~pit(i,j)) is True and self.kb.ask_if_true(wumpus(i,j) | pit(i,j)) is False:
                        self.findPath(x,y,i,j)
                        self.action = self.plan.pop(0)
                        flag = False
                        break
                if flag is False:
                    break
                        

        self.TakeAction(self.action) 
        return self.PL_Wumpus_Agent()
    
    def findPath(self, x,y, a,b):
        q = collections.deque()
        src = Node(x, y, None)
        q.append(src)

        visited_nodes = set()

        key = (src.x, src.y)
        visited_nodes.add(key)

        row = [-1, 0, 0, 1]
        col = [0, -1, 1, 0]

        while q:
            curr = q.popleft()
            i, j = curr.x, curr.y

            if i == a and j == b:
                return self.getPlan(curr)
            
            idxi, idxj = self._FindIndicesForLocation([i,j])

            if self.visited[idxi][idxj] is False:
                continue

            for k in range(4):
                x = i + row[k]
                y = j + col[k]
    
                if x in range(1,5) and y in range(1,5):
                    next = Node(x, y, curr)
                    key = (next.x, next.y)
                    if key not in visited_nodes:
                        q.append(next)
                        visited_nodes.add(key)

        return None
    
    def getPlan(self, node):
        if node is None:
            return 

        self.getPlan(node.parent)
        
        if node.parent is None:
            return
        if node.parent.x > node.x:
            self.plan.append("Left")
        elif node.parent.x < node.x:
            self.plan.append("Right")
        elif node.parent.y > node.y:
            self.plan.append("Down")
        else:
            self.plan.append("Up")
        
        return
                    
class Node:
    def __init__(self, x, y, parent):
        self.x = x
        self.y = y
        self.parent = parent
    
    def __repr__(self):
        return str((self.x, self.y))


def main():
    ag = Agent()
    ag.PL_Wumpus_Agent()
    print("dpll_calls:", dpll_calls)
    print("Sequence visited:", seq_rooms_visited)

if __name__=='__main__':
    main()