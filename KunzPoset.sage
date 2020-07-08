from sage.combinat.posets.posets import FinitePoset
import re

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

    def __init__(self, m, cover_relations = None, hyperplane_desc = None, \
            semigroup_gens = None, numerical_semigroup = None, apery_set = None, \
            kunz_coordinates = None):
        """
        ----------
        Parameters
        ----------
        """

        # Set the multiplicity for our KunzPoset
        self.m = m

        # Assuming cover_relations is list of lists
        # Implementation for dictionary later
        if (cover_relations is not None):
            self.cover_relations = [(i,j) for (i,j,k) in \
                    DiGraph(cover_relations).transitive_reduction().edges()]
            self.hyperplane_desc = self.__generate_h_desc()

        # Hyperplane description will be a list of lists
        elif (hyperplane_desc is not None):
            self.hyperplane_desc = hyperplane_desc
            self.cover_relations = self.__generate_cover_relations()

        # This should just be a list or a tuple
        elif (semigroup_gens is not None):
            self.semigroup_gens = semigroup_gens
            self.cover_relations = self.__generate_cover_relations()
            self.hyperplane_desc = self.__generate_h_desc()

        elif (numerical_semigroup is not None):
            self.S = numerical_semigroup
            self.semigroup_gens = self.S.gens
            self.cover_relations = self.__generate_cover_relations()
            self.hyperplane_desc = self.__generate_h_desc()

        elif (apery_set is not None):
            self.apery_set = apery_set
            self.cover_relations = self.__generate_cover_relations()
            self.hyperplane_desc = self.__generate_h_desc()

        elif (kunz_coords is not None):
            self.kunz_coords = kunz_coords
            self.cover_relations = self.__generate_cover_relations()
            self.hyperplane_desc = self.__generate_h_desc()

        else:
            raise ValueError('You did not pass data for the KunzPoset.')

        # Make the poset
        self.poset = self.__generate_poset()

        # atoms of the poset
        self.atoms = [j for (i,j) in self.cover_relations if (i == 0)]

    # When someone puts object in a print statement
    def __repr__(self):
        return "KunzPoset with multiplicity %d." % self.m

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
        if (not hasattr(self, "__face")):
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
        if (not hasattr(self, "__factorizations")):
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
        if (not hasattr(self, '__factorizations')):
            self.__make_factorizations()
        if (not hasattr(self, '__bettis')):
            self.__find_num_bettis_graph()
        return self.__bettis

    def BettiMatrix(self):
        if (not hasattr(self, '__factorizations')):
            self.__make_factorizations()
        if (not hasattr(self, '__bettis')):
            self.__find_num_bettis_graph()

        return self.__betti_matrix

    def __make_relation_matrix(self):
        betti_matrix = []
        for betti in self.__bettis:
            for relations in self.__bettis[betti]:
                betti_matrix.append([rel for rel in relations])

        self.__betti_matrix = matrix(betti_matrix)

    def Dimension(self):
        if (not hasattr(self, '__factorizations')):
            self.__make_factorizations()
        if (not hasattr(self, '__bettis')):
            self.__find_num_bettis_graph()

        return len(self.atoms) - self.__betti_matrix.rank()

    '''
        This static method expects there to be a data.out file in the same
        directory called 'data.out'. You can change the file_path parameter
        to change the location of this file. This file contains the list of
        hyperplanes defining the Kunz Polyhedra you are looking at. The face_desc
        is a string containing 1's and 0's to tell KunzPoset which hyperplanes
        should be used to build the KunzPoset.
    '''
    @staticmethod
    def BuildFromNormaliz(face_desc, hplane_file_path='data.out'):
        hyperplane_list = []

        f = open(hplane_file_path, 'r')
        lines = f.readlines()
        f.close()
        check = re.compile(r'^(\s(-|\s)\d)+$')

        for line in lines:
            if re.match(check, line) is not None:
                ineq = list(map(int, line.split()))
                hyperplane_list.append(ineq)

        hyperplane_desc = []
        for index, equality in enumerate(face_desc):
            if(int(equality)):
                hyperplane_desc.append(hyperplane_list[index])

        multiplicity = len(hyperplane_desc[0]) + 1
        return KunzPoset(m=multiplicity, hyperplane_desc=hyperplane_desc)

    # @staticmethod
    # def FaceLatticeFromNormaliz(m, face_lattice_file_path='data.fac'):
    #     file_name = face_lattice_file_path
    #     f = open(file_name, 'r')
    #     lines = f.readlines()[3:]
    #     f.close()

    #     equalities = []
    #     for line in lines:
    #         equalities.append(line.split()[0])
    #     return(equalities)
