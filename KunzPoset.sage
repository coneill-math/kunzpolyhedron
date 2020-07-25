from sage.combinat.posets.posets import FinitePoset
import re
import heapq, queue


class KunzPoset:
    """
        A class used to represent a KunzPoset object.

        ----------
        Attributes
        ----------

        m : int
            The multiplicity of our KunzPoset
        cover_relations : List of Tuples
            The cover relations of our KunzPoset
        hyperplane_desc : List of Lists
            The inequalities that describe our KunzPoset
        poset : FinitePoset
            Visual representation of our KunzPoset
        atoms : List
            List of the bottom-most elements of our KunzPoset (excluding 0)

        -------------------
        Optional Attributes
        -------------------

        apery_set : List
            The apery_set of a Numerical Semigroup
        kunz_coords : List
            The Kunz Coordinates of a Numerical Semigroup

        *The Following Require NumericalSemigroup.sage*
        Download at https://github.com/coneill-math/numsgps-sage

        S : NumericalSemigroup
            The Numerical Semigroup whose Apery
        semigroup_gens : List
            The minimal generators of the Numerical Semigroup whose Apery Poset
            is our KunzPoset
    """

    def __init__(self, m = None, cover_relations = None, hyperplane_desc = None, \
            semigroup_gens = None, numerical_semigroup = None, apery_set = None, \
            kunz_coordinates = None, poset = None):
        """
        ----------
        Parameters
        ----------
        """

        # Assuming cover_relations is list of lists
        # Implementation for dictionary later
        if (cover_relations is not None):
            if m is None:
                raise ValueError('You did not pass the multiplicity for the KunzPoset.')
            self.m = m
            self.cover_relations = [(i,j) for (i,j,k) in \
                    DiGraph(cover_relations).transitive_reduction().edges()]
            self.hyperplane_desc = self.__generate_h_desc()

        # Hyperplane description will be a list of lists
        elif (hyperplane_desc is not None):
            if m is None:
                raise ValueError('You did not pass the multiplicity for the KunzPoset.')
            self.m = m
            self.hyperplane_desc = list(hyperplane_desc)
            self.cover_relations = self.__generate_cover_relations()

        # This should just be a list or a tuple
        elif (semigroup_gens is not None):
            self.m = min(semigroup_gens)
            self.semigroup_gens = list(semigroup_gens)
            self.cover_relations = self.__generate_cover_relations()
            self.hyperplane_desc = self.__generate_h_desc()

        elif (numerical_semigroup is not None):
            self.m = min(numerical_semigroup.gens)
            self.S = numerical_semigroup
            self.semigroup_gens = self.S.gens
            self.cover_relations = self.__generate_cover_relations()
            self.hyperplane_desc = self.__generate_h_desc()

        elif (apery_set is not None):
            self.m = len(apery_set)
            self.apery_set = list(apery_set)
            self.cover_relations = self.__generate_cover_relations()
            self.hyperplane_desc = self.__generate_h_desc()

        elif (kunz_coordinates is not None):
            self.m = len(kunz_coordinates) + 1
            self.kunz_coords = list(kunz_coordinates)
            self.cover_relations = self.__generate_cover_relations()
            self.hyperplane_desc = self.__generate_h_desc()

        elif (poset is not None):
            self.m = len(poset)
            self.poset = poset
            self.cover_relations = poset.cover_relations()
            self.hyperplane_desc = self.__generate_h_desc()

        else:
            raise ValueError('You did not pass data for the KunzPoset.')

        # Make the poset
        self.poset = self.__generate_poset()

        # atoms of the poset
        self.atoms = [j for (i,j) in self.cover_relations if (i == 0)]

    # When someone puts object in a print statement
    def __repr__(self):
        return "KunzPoset with multiplicity %d" % self.m

    def __eq__(self, P):
        return self.poset == P.poset

    def __hash__(self):
        return hash(self.poset)

    def __generate_cover_relations(self):
        if (hasattr(self, "kunz_coords")):
            self.apery_set = [self.m * coord + i \
                for i, coord in enumerate(kunz_coords)]

        # Means we are calling from apery_set if statement
        if (hasattr(self, "apery_set")):
            apery_set = copy(self.apery_set)
            apery_set.sort(reverse=True)
            apery_set.pop()
            sums = [a_i + a_j for a_i in apery_set for a_j in apery_set]
            atoms = set(apery_set) - (set(sums) & set(apery_set))
            covers = [(a_i % self.m, a_j % self.m) for a_i in apery_set \
                for a_j in apery_set if a_j - a_i in atoms]
            covers += [(0, a % self.m) for a in atoms]
            return [(i,j) for (i,j,k) in \
                    DiGraph(covers).transitive_reduction().edges()]

        # Means we are calling from semigroup_gens if statement
        elif (not hasattr(self, "hyperplane_desc")):
            if (not hasattr(self, "S")):
                try:
                    self.S = NumericalSemigroup(self.semigroup_gens)
                except:
                    print("You need NumericalSemigroup package")
                    return

            apery_set = self.S.AperySet(self.m)
            covers = []

            for i, a_i in enumerate(apery_set):
                cover = [i]
                for j, a_j in enumerate(apery_set):
                    if (a_j - a_i in self.S and i != j):
                        covers.append([i,j])
            return [(i,j) for (i,j,k) in \
                    DiGraph(covers).transitive_reduction().edges()]

        # Means we are calling from hyperplane_desc if statement
        # Assuming h_desc does not have the zero column
        else:
            relations = []
            for ieq in self.hyperplane_desc:
                relation = []
                for index, element in enumerate(ieq):
                    if (element == 1):
                        relation.append(index + 1)
                    elif (element == 2):
                        relation += 2 * [index + 1]
                    elif (element == -1):
                        result = index + 1

                relation.append(result)
                relations.append(relation)

            rels = [(i,k) for (i,j,k) in relations] + \
                   [(j,k) for (i,j,k) in relations]
            zero = [(0,n) for n in range(1, self.m)]
            rels += zero
            return [(i,j) for (i,j,k) in \
                    DiGraph(rels).transitive_reduction().edges()]


    # Generate the hyperplane description
    # Assuming cover relations have already been computed
    def __generate_h_desc(self):
        relations = copy(self.cover_relations)
        full_relations = []
        seen_relations = []

        while len(relations) > 0:
            if (relations[0][0] == 0):
                relations.pop(0)
            elif (tuple(relations[0]) in seen_relations):
                relations.pop(0)
            else:
                full_relation = (relations[0][0], \
                        (relations[0][1] - relations[0][0]) % self.m, \
                        relations[0][1])
                seen_relations.append(((relations[0][1] - relations[0][0]) \
                        % self.m, relations[0][1]))
                full_relations.append(full_relation)
                relations.pop(0)

        h_desc = []

        for full_relation in full_relations:
            ieq = (self.m - 1) * [0]
            ieq[full_relation[0] - 1] += 1
            ieq[full_relation[1] - 1] += 1
            ieq[full_relation[2] - 1] = -1
            h_desc.append(ieq)

        return h_desc

    # generating the poset
    def __generate_poset(self):
        return FinitePoset(DiGraph(self.cover_relations).transitive_reduction())

    def Face(self):
        if (not hasattr(self, "_KunzPoset__face")):
            self.__face = Polyhedron(self.hyperplane_desc)
        return self.__face

    def __make_factorizations(self, VERBOSE = False):
        # Need minimal gens and order in which to check elements
        minimal_elements = self.atoms
        order = self.poset.linear_extension()

        # Declare dictionaries
        gen_index = {}
        factorizations = {}

        # Know which index to increment
        for i, gen in enumerate(minimal_elements):
            gen_index.setdefault(gen, i)

        # Main nested for loop
        for element in order:
            factorizations.setdefault(element, [])

            # Check each generator
            for gen in minimal_elements:
                if element == 0:
                    factorizations[element].append([0] * len(minimal_elements))
                    break

                difference = (element - gen) % self.m
                if (self.poset.compare_elements(element, difference) == 1):
                    for factorization in factorizations[difference]:
                        temp = copy(factorization)
                        temp[gen_index[gen]] += 1
                        if (temp not in factorizations[element]):
                            factorizations[element].append(temp)

        self.__factorizations = factorizations

    def Factorization(self, element = None):
        if (not hasattr(self, "_KunzPoset__factorizations")):
            self.__make_factorizations()
        return self.__factorizations[element] if element is not None else \
                self.__factorizations

    # Function needed for find_num_bettis_graph
    def __generate_bin(self, num_list):
        return '0b' + ''.join(['1' if num > 0 else '0' for num in num_list])

    def __find_num_bettis_graph(self, VERBOSE = False):
        bettis = {}

        for element, factorization in self.__factorizations.items():
            # Only go through process if more than one factorization exists
            # for an element of the poset
            if (len(factorization) > 1):
                # initialize both representations
                binary_rep = [self.__generate_bin(factorization[0])]
                real_rep = [[factorization[0]]]

                # Test each new relation against others
                for rel in factorization[1:]:
                    binary_rel = self.__generate_bin(rel)
                    groups_added_to = []
                    i = 0

                    # Compare new relation aginst others already grouped
                    while (i < len(real_rep)):
                        binary_add = int(binary_rep[i],2) & int(binary_rel,2)
                        if (binary_add != 0):
                            groups_added_to.append(i)

                        i += 1

                    # Goes through and connects groups that are now connected
                    # through new relation
                    if (len(groups_added_to) > 1):
                        start = groups_added_to[0]
                        for i in range(len(groups_added_to)-1, 0, -1):
                            index = groups_added_to[i]

                            real_rep[start] += real_rep[index]
                            binary_rep[start] = bin(int(binary_rep[start],2) \
                                                  | int(binary_rep[index],2))

                            real_rep.pop(index)
                            binary_rep.pop(index)

                        real_rep[start] += [rel]
                        binary_rep[start] = bin(int(binary_rep[start],2) | \
                                                int(binary_rel,2))

                    # Adds the relation to the group it belongs to
                    elif (len(groups_added_to) == 1):
                        index = groups_added_to[0]
                        binary_rep[index] = bin(int(binary_rep[index],2) | \
                                                int(binary_rel,2))
                        real_rep[index].append(rel)

                    # Creates a new group since the new relation was not
                    # connected to anything
                    else:
                        binary_rep.append(binary_rel)
                        real_rep.append([rel])

                # Connect the different groups
                if (len(real_rep) > 1):
                    bettis[element] = []
                    for rep in real_rep[1:]:
                        relation = list(map(operator.sub, real_rep[0][0], rep[0]))
                        bettis[element].append(relation)

        self.__bettis = bettis
        self.__make_relation_matrix()

    def BettiElements(self):
        if (not hasattr(self, '_KunzPoset__factorizations')):
            self.__make_factorizations()
        if (not hasattr(self, '_KunzPoset__bettis')):
            self.__find_num_bettis_graph()
        return self.__bettis

    def BettiMatrix(self):
        if (not hasattr(self, '_KunzPoset__factorizations')):
            self.__make_factorizations()
        if (not hasattr(self, '_KunzPoset__bettis')):
            self.__find_num_bettis_graph()

        return self.__betti_matrix

    def __make_relation_matrix(self):
        betti_matrix = []
        for betti in self.__bettis:
            for relations in self.__bettis[betti]:
                betti_matrix.append([rel for rel in relations])

        self.__betti_matrix = matrix(betti_matrix)
    
    def MinimalPresentation(self):
        thematrix = self.BettiMatrix()
        
        return [[[(r if r >= 0 else 0) for r in row], [(-r if r <= 0 else 0) for r in row]] for row in thematrix.rows()]

    def Dimension(self):
        if (not hasattr(self, '_KunzPoset__dimension')):
            if (not hasattr(self, '_KunzPoset__factorizations')):
                self.__make_factorizations()
            if (not hasattr(self, '_KunzPoset__bettis')):
                self.__find_num_bettis_graph()

            self.__dimension = len(self.atoms) - self.__betti_matrix.rank()
        
        return self.__dimension
    
    def __outerelementinfo(self, upper_factorizations):
        # TODO: build poset too
        factlistsbyfacts = {}
        outerposetelements = []
        outerposetcoverrelations = []
        minpreselements = []
        outerminrelations = []
        allfacts = queue.Queue()
        
        for p in self.poset.linear_extension():
            factlist = [list(sorted([tuple(f) for f in self.Factorization(p)])), []]
            outerposetelements.append(factlist)
            
            for f in factlist[0]:
                factlistsbyfacts[tuple(f)] = len(outerposetelements) - 1
                for i in range(len(f)):
                    f2 = list(f)
                    f2[i] = f2[i] + 1
                    allfacts.put(tuple(f2))
        
        upperfacts = set([tuple(f) for f in upper_factorizations if tuple(f) not in factlistsbyfacts])
        
        def parsenext(f):
            factlist = [[f], []]
            nextcovers = []
            gensbacked = []
            runagain = True
            
            while runagain:
                runagain = False
                for i in range(len(f)):
                    if i in gensbacked:
                        continue
                    
                    for ff in factlist[0]:
                        if ff[i] > 0:
                            break
                    
                    if ff[i] == 0:
                        continue
                    
                    runagain = True
                    gensbacked = gensbacked + [i]
                    
                    backone = list(ff)
                    backone[i] = backone[i] - 1
                    
                    if tuple(backone) not in factlistsbyfacts:
                        return ([],[])
                    
                    cover = factlistsbyfacts[tuple(backone)]
                    nextcovers.append(cover)
                    
                    for j in [0,1]:
                        for ff2 in outerposetelements[cover][j]:
                            ff3 = list(ff2)
                            ff3[i] = ff3[i] + 1
                            
                            factlist[j].append(tuple(ff3))
            
            factlist[0] = list(set(factlist[0]))
            factlist[1] = list(set(factlist[1]))
            
            if len(factlist[1]) == 0:
                elem = sum([a*fi for (a,fi) in zip(self.atoms,f)]) % self.m
                if list(f) not in self.Factorization(elem):
                    factlist[1] = factlist[1] + [tuple(f2) for f2 in self.Factorization(elem)]
            
            return (factlist, nextcovers)
        
        while len(upperfacts) > 0:
            f = allfacts.get()
            
            if f in factlistsbyfacts:
                continue
            
            (factlist, nextcovers) = parsenext(f)
            
            if factlist == []:
                continue
            
            newindex = len(outerposetelements)
            isnew = True
            isminpres = False
            
            # indicates this has a minmal relation
            if all(cover < self.m for cover in nextcovers):
                isminpres = True
                outerminrelations.append([[0] + list(factlist[0][0]), [1] + list(factlist[1][0])])
                for elem in minpreselements:
                    leftfact = outerposetelements[elem][0][0]
                    rightfact = factlist[0][0]
                    thevec = vector([a-b for (a,b) in zip(leftfact, rightfact)])
                    try:
                        self.BettiMatrix().solve_left(thevec)
                    except ValueError as e:
                        continue
                    
                    # these are secretly the same element
                    isnew = False
                    newindex = elem
                    outerposetelements[elem][0] = outerposetelements[elem][0] + factlist[0]
                    break
            
            if isnew:
                outerposetelements.append(factlist)
            
            if isnew and isminpres:
                minpreselements.append(newindex)
            
            outerposetcoverrelations = outerposetcoverrelations + [(c, newindex) for c in nextcovers]
            for ff in factlist[0]:
                factlistsbyfacts[ff] = newindex
                if ff in upperfacts:
                    upperfacts.remove(ff)
            
            # add next things to try
            for i in range(len(f)):
                f2 = list(f)
                f2[i] = f2[i] + 1
                allfacts.put(tuple(f2))
        
        for (op,factlist) in enumerate(outerposetelements):
            unifiedfacts = [(0,) + ff for ff in factlist[0]]
            unifiedfacts = unifiedfacts + [(1,) + ff for ff in factlist[1]]
            outerposetelements[op] = unifiedfacts
        
        outerposet = Poset((list(range(len(outerposetelements))), outerposetcoverrelations), cover_relations=True)
        
        return (outerposet, outerposetelements, minpreselements, outerminrelations)
    
    def OuterElementPoset(self, upper_factorizations = None):
        if upper_factorizations is None:
            upper_factorizations = [tuple([fi+1 for fi in f]) for p in self.poset.maximal_elements() for f in self.Factorization(p)]
        
        (outerposet, outerposetelements, outerminpreselements, outerminrelations) = self.__outerelementinfo(upper_factorizations)
        
        return (outerposet, outerposetelements)
    
    def FullMinimalPresentation(self, kunz_coords = None):
        upper_factorizations = [tuple([(fi+1 if i == j else fi) for (i,fi) in enumerate(self.Factorization(p)[0])]) for p in self.poset.maximal_elements() for j in range(len(self.atoms))]
        
        (outerposet, outerposetelements, outerminpreselements, outerminrelations) = self.__outerelementinfo(upper_factorizations)
        
        ret = [[[0] + p1, [0] + p2] for [p1,p2] in self.MinimalPresentation()]
        
        for [leftfact, rightfact] in outerminrelations:
            if kunz_coords is not None:
                rightfact[0] = sum([(b-c)*kunz_coords[a2-1] for (a2,b,c) in zip(self.atoms, leftfact[1:], rightfact[1:])])
                rightfact[0] = rightfact[0] + sum([(b-c)*a2 for (a2,b,c) in zip([0]+self.atoms, leftfact, rightfact)])/self.m
            
            ret.append([leftfact, rightfact])
        
        return ret
    
    def OuterBettiFactorizationSets(self):
        upper_factorizations = [tuple([fi+1 for fi in f]) for p in self.poset.maximal_elements() for f in self.Factorization(p)]
        
        (outerposet, outerfacts, outerminpreselements, outerminrelations) = self.__outerelementinfo(upper_factorizations)
        
        ret = {d:[] for d in range(len(self.atoms))}
        for op in outerposet:
            factlist = outerfacts[op]
            sdc = SimplicialComplex(maximal_faces=[[i for i in range(len(f)) if f[i] > 0] for f in factlist], maximality_check=True)
            hom = sdc.homology()
            for d in range(len(hom)):
                if len(hom[d].gens()) > 0:
                    ret[d] = ret[d] + [factlist]*len(hom[d].gens())
        
        return ret
    
    def OuterBettiElements(self):
        outerbettifacts = self.OuterBettiFactorizationSets()
        return {d:list(sorted([sum([a*b for (a,b) in zip([0]+self.atoms,factlist[0])])%self.m for factlist in outerbettifacts[d]])) for d in range(len(self.atoms))}
    
    def Orbit(self):
        m = self.m
        return [KunzPoset(poset=self.poset.relabel([(i*u)%m for i in range(m)])) for u in range(1,m) if gcd(u,m) == 1]
    
    def FindSemigroups(self, max_kunz_coord, how_many, min_kunz_coord = 2):
        m = self.m
        atoms = self.atoms
        poset = self.poset
        trucks = []
        modulus_fails = 0
        total_attempts = 0
        
        if self.Dimension() == len(atoms):
            while len(trucks) < how_many:
                total_attempts = total_attempts + 1
                temp_gens = [m]
                for ii in atoms:
                    noop= random.randint(min_kunz_coord , max_kunz_coord)*m + ii
                    temp_gens.append(noop)
                if not sorted([y%m for y in temp_gens]) == sorted([0] + atoms):
                    modulus_fails = modulus_fails + 1
                    if modulus_fails >= 1000 and modulus_fails == total_attempts:
                        print("Likely contains no semigroups")
                        return []
                    continue
                    
                if gcd(temp_gens) == 1:
                    kpp = KunzPoset(m, semigroup_gens=temp_gens).poset
                    if kpp == poset:
                        trucks.append(temp_gens)
        else:
            pres = matrix(QQ, self.BettiMatrix())
            pres.echelonize()
            while len(trucks) < how_many:
                total_attempts = total_attempts + 1
                temp = [0]*len(atoms)
                temp_gens = [m]
                for i in pres.nonpivots():
                    boop = random.randint(min_kunz_coord , max_kunz_coord)*m + atoms[i]
                    temp[i] = boop
                    temp_gens.append(int(boop))
                vec = vector(temp)
                othervars = pres*vec
                # print(othervars)
                for jj in othervars: 
                    temp_gens.append(int(-1*jj))
                # print(temp_gens)
                if list(sorted([y%m for y in temp_gens])) != list(sorted([0] + atoms)):
                    modulus_fails = modulus_fails + 1
                    if modulus_fails >= 10000 and modulus_fails == total_attempts:
                        print("Likely contains no semigroups")
                        return []
                    continue
                if gcd(temp_gens) == 1 and all(x>0 for x in temp_gens):
                    kpp = KunzPoset(m, semigroup_gens=temp_gens).poset
                    #kpp.show()
                    if kpp == poset:
                        trucks.append(temp_gens)
                    else:
                        continue
                else:
                    continue
        return trucks
    
    '''
        This static method expects there to be a data.out file in the same
        directory called 'data.out'. You can change the file_path parameter
        to change the location of this file. This file contains the list of
        hyperplanes defining the Kunz Polyhedra you are looking at. The face_desc
        is a string containing 1's and 0's to tell KunzPoset which hyperplanes
        should be used to build the KunzPoset.
    '''
    @staticmethod
    def BuildFromNormaliz(face_desc, hyperplane_list=None, hplane_file_path='data.out'):
        if hyperplane_list == None:
            hyperplane_list = KunzPoset.ReadHyperplanesFromNormaliz(hplane_file_path)
        
        hyperplane_desc = []
        for index, equality in enumerate(face_desc):
            if(int(equality)):
                hyperplane_desc.append(hyperplane_list[index])

        multiplicity = len(hyperplane_list[0]) + 1
        return KunzPoset(m=multiplicity, hyperplane_desc=hyperplane_desc)

    @staticmethod
    def ReadHyperplanesFromNormaliz(hplane_file_path='data.out'):
        check = re.compile(r'^(\s(-|\s)\d)+$')
        hyperplane_list = []
        
        with open(hplane_file_path, 'r') as f:
            for line in f:
                if re.match(check, line) is not None:
                    ineq = list(map(int, line.split()))
                    hyperplane_list.append(ineq)
        
        return hyperplane_list

    @staticmethod
    def ReadFacesFromNormaliz(face_lattice_file_path='data.fac', hplane_file_path='data.out', faceindices=None, dimension=None):
        hyperplane_list = KunzPoset.ReadHyperplanesFromNormaliz(hplane_file_path)
        multiplicity = len(hyperplane_list[0]) + 1
        M = max(faceindices) if faceindices != None else oo
        
        faces = []
        
        file_name = face_lattice_file_path
        with open(file_name, 'r') as f:
            f.readline()
            f.readline()
            f.readline()
            
            curindex = -1
            for line in f:
                curindex = curindex + 1
                
                if curindex > M:
                    break
                
                if faceindices != None and curindex not in faceindices:
                    continue
                
                (face, d) = tuple(line.split())
                dim = multiplicity - 1 - int(d)
                
                if dimension != None and dim != dimension:
                    curindex = curindex - 1
                    continue
                
                try:
                    P = KunzPoset.BuildFromNormaliz(face, hyperplane_list)
                    P.__dimension = dim
                    faces.append(P)
                except ValueError as e:
                    if str(e) == "Hasse diagram contains cycles":
                        pass
                    else:
                        raise
        
        return faces
