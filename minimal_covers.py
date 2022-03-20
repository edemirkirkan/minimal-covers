
import itertools
import random

## Q1a. Determine the closure of a given set of attribute S the schema R and functional dependency F
def closure(R, FD, S):
    '''
    Check each functional dependency X -> Y on each iteration and add Y to the closure iff 
    X is a subset of the closure formed so far, repeat until there is no change in the set
    '''
    if not (is_subset(S, R)):
        return [] 
    result = list(S)
    changed = True
    while (changed):
        changed = False
        for fd in FD:
            LHS = fd[0]
            RHS = fd[1]
            if (is_subset(LHS, result)):
                for att in RHS:
                    if (att not in result):
                        result.append(att)
                        changed = True
    return sorted(result)


## Q1b. Determine all attribute closures excluding superkeys that are not candidate keys given the schema R and functional dependency F
def all_closures(R, FD): 
    '''
    Calculate closure of each attribute susbset of the schema unless the subset is superkey 
    but not candidate key. Check in each iteration if the attribute closure equals to R, 
    that is, check for candidate key, and if it is not minimal then just continue 
    with the next iteration instead of appending closure to the result set
    '''
    result = []
    candidate_keys = []
    for att_set in subsets(R):
        att_closure = closure(R, FD, att_set)
        if (att_closure == R):
            is_super = False
            for key in candidate_keys:
                if is_subset(key, att_set):
                    is_super = True
            if is_super:
                continue
            candidate_keys.append(att_set)
        result.append([att_set, att_closure])
    return result


## Q2a. Return a minimal cover of the functional dependencies of a given schema R and functional dependencies F.
def min_cover(R, FD):
    '''
    1) Simplfy right side of each FD, i.e. X -> YZ becomez X -> Y and X -> Z
    2) Simplify left side of each FD i.e. XY -> Z and if X already haz Z on its closure, 
    then X -> Z, or vice versa X -> Y, XY -> Z otherwise
    3) Eliminate duplicate FDs first, then check for redundant FDs and eliminate them, 
    finally eliminate extraneous attributes on each FD if exists
    '''
    FD1 = find_sigma1(FD)
    FD2 = find_sigma2(R, FD, FD1)
    FD3 = find_sigma3(R, random.choice(FD2))
    return FD3


## Q2b. Return all minimal covers reachable from the functional dependencies of a given schema R and functional dependencies F.
def min_covers(R, FD):
    '''
    1) Simplfy right side of each FD, i.e. X -> YZ becomez X -> Y and X -> Z
    2) Simplify left side of each FD i.e. XY -> Z and if X already haz Z on its closure, 
    then X -> Z, or vice versa X -> Y, XY -> Z otherwise
    Put into a list of all different products of the possibilities
     which can be vary according to choice of X -> Z or X -> Y or XY -> Z
    3) Eliminate duplicate FDs first, then check for redundant FDs and eliminate them, 
    finally eliminate extraneous attributes on each FD if exists
    '''
    FD1 = find_sigma1(FD)
    FD2 = find_sigma2(R, FD, FD1)
    FD3 = []
    for fd in FD2:
        FD3.append(find_sigma3(R, fd))
    return FD3

## Helper functions
def is_subset(X, Y):
    '''
    Check if the list is subset of another list
    '''
    return set(X).issubset(set(Y)) 

def subsets(R):
    '''
    Calculate all possible subsets of given list
    Return them in a sorted way (first alphabetic and then length)
    '''
    x = len(R)
    masks = [1 << i for i in range(x)]
    result = []
    for i in range(1, 1 << x):
        r = []
        for mask, ss in zip(masks, R):
            if i & mask:
                r.append(ss)
        result.append(r)  
    result.sort() 
    result.sort(key=len) 
    return result

def find_sigma1(FD):
    '''
    Divide RHS of each FD and add the products to the new FD set, 
    i.e. {X -> YZ, X -> Z} -> {X -> Y, X -> Z, X -> Z}
    '''
    FD1 = []
    for fd in FD:
        rhs_size = len(fd[1])
        if (rhs_size <= 1):
            FD1.append(fd)
        else:
            for att in fd[1]:
                FD1.append([fd[0], [att]])
    return FD1


def find_sigma2(R, FD, FD1):
    '''
    Simplify left side of each FD i.e. XY -> Z and if X already haz Z on its closure,
     then X -> Z, or vice versa X -> Y, XY -> Z otherwise
    Algorithm first decide all possible outcome of each FD and put them into a list,
     then take cross product of all lists in the formed list
    '''
    all_possible_fds = []
    FD2 = []
    for fd in FD1:
        possible_fds = []
        lhs_size = len(fd[0])
        if (lhs_size <= 1):
                possible_fds.append(fd)
        else:
            found = False
            for att in fd[0]:
                if fd[1][0] in closure(R, FD, [att]):
                    found = True
                    possible_fds.append([[att], [fd[1][0]]])
            if not found:
                possible_fds.append(fd)
        all_possible_fds.append(possible_fds)

    for tup in itertools.product(*all_possible_fds):
        FD2.append(list(tup))
    return FD2


def find_sigma3(R, FD2):
    '''
    1) Remove all duplicates remaining from sigma2
    2) Remove all redundant fds by checking iff 
    the rhs still implied in the absence of fd, if yes remove
    3) Remove extraneous attributes by checking iff 
    the closure is still contains the attribute within the absence of attribute
    '''
    FD3 = remove_duplicates(FD2)
    FD3 = remove_redundant_fd(R, FD3)
    FD3 = remove_extraneous_att(R, FD3)

    return FD3

def remove_duplicates(FD):
    '''
    Remove all duplicates from the fd set
    '''
    FD2 = list(FD)
    FD2.sort()
    FD2 = list(FD2 for FD2,_ in itertools.groupby(FD2))
    return FD2

def remove_redundant_fd(R, FD):
    '''
    Remove all redundant fds by checking if the rhs still 
    implied in the absence of fd, if yes remove
    '''
    for fd in FD:
        FD2 = list(FD)
        FD2.remove(fd)
        if is_subset(fd[1], closure(R, FD2, fd[0])):
            FD.remove(fd)
    return FD

def remove_extraneous_att(R, FD):
    '''
    Remove extraneous attributes by checking if the closure is 
    still contains the attribute within the absence of attribute
    '''
    for fd in FD:
        for att in fd[0]:
            if is_subset(att, closure(R, FD, [n for n in fd[0] if n != att])):
                fd[0].remove(att)   
    return FD

## Main functions
def main():

    R = ['A', 'B', 'C', 'D', 'E']
    FD = [[['B'], ['A']], [['A', 'C'], ['B', 'D', 'E']]]
    print(all_closures(R, FD)) 




if __name__ == '__main__':
    main()
