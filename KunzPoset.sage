from sage.numerical.mip import MixedIntegerLinearProgram
from sage.combinat.posets.posets import FinitePoset
import re
import heapq, queue

import itertools, random
from multiprocessing import Pool


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
		cone_coordinates : List
			The coordinates of a point in the Kunz cone

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
			kunz_coordinates = None, cone_coordinates = None, poset = None):
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
			self.hyperplane_desc = [tuple(hyp) for hyp in hyperplane_desc]
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

		elif (cone_coordinates is not None):
			if cone_coordinates[0] == 0:
				cone_coordinates = cone_coordinates[1:]
			self.m = len(cone_coordinates) + 1
			self.cone_coordinates = list(cone_coordinates)
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
		
		elif (hasattr(self, "cone_coordinates")):
			cone_coordinates = [0] + self.cone_coordinates
			rels = [(i,j) for i in range(self.m) for j in range(self.m) if i != j and cone_coordinates[i] + cone_coordinates[(j-i) % self.m] == cone_coordinates[j]]
			return [(i,j) for (i,j,k) in \
					DiGraph(rels).transitive_reduction().edges()]

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
			h_desc.append(tuple(ieq))

		return h_desc

	# generating the poset
	def __generate_poset(self):
		return FinitePoset(DiGraph(self.cover_relations).transitive_reduction())

	def Face(self):
		if (not hasattr(self, "_KunzPoset__face")):
			ieqs = KunzPoset.KunzInequalities(self.m)
			eqns = [[0] + list(eqn) for eqn in self.hyperplane_desc]
			self.__face = Polyhedron(ieqs=ieqs, eqns=eqns)
		return self.__face
	
	def FanFace(self):
		minpres = self.MinimalPresentation()
		obs = self.OuterBettiElements()
		
		eqns = [[0] + list(vector(rel[0]) - vector(rel[1])) for rel in minpres]
		
		ieqs = []
		for ob in obs:
			element = sum([a*b for (a,b) in zip(self.atoms, ob[0])]) % self.m
			fact = self.Factorization(element)[0]
			ieqs.append([0] + list(vector(ob[0]) - vector(fact)))
		
		return Polyhedron(ieqs=ieqs, eqns=eqns)
	
	def FacetPosets(self, allow_nontrivial_subgroup=True):
		fanface = self.FanFace()
		
		ret = []
		for F in fanface.faces(fanface.dim()-1):
			pt = list(sum([vector(ray) for ray in F.rays()]))
			
			coords = []
			for i in range(1,self.m):
				coords.append(sum([a*b for (a,b) in zip(self.Factorization(i)[0], pt)]))
			
			if min(coords) == 0:
				if allow_nontrivial_subgroup:
					coords = coords[:coords.index(0)]
				else:
					continue
			
			newposet = KunzPoset(cone_coordinates=coords)
			ret.append(newposet)
		
		return ret

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
	
	def FullMinimalPresentation(self, kunz_coords = None, cone_coords = None):
		outerfacts = self.OuterBettiElements()
		
		ret = [[[0] + p1, [0] + p2] for [p1,p2] in self.MinimalPresentation()]

		for betti in outerfacts:
			leftfact = [0] + list(betti[0])
			rightfact = [1] + self.Factorization(sum([self.atoms[i]*f for (i,f) in enumerate(betti[0])]) % self.m)[0]
			if kunz_coords is not None:
				rightfact[0] = sum([(b-c)*kunz_coords[a2-1] for (a2,b,c) in zip(self.atoms, leftfact[1:], rightfact[1:])])
				rightfact[0] = rightfact[0] + sum([(b-c)*a2 for (a2,b,c) in zip([0]+self.atoms, leftfact, rightfact)])/self.m
			if cone_coords is not None:
				rightfact[0] = sum([(b-c)*cone_coords[a2-1] for (a2,b,c) in zip(self.atoms, leftfact[1:], rightfact[1:])])/self.m
			
			ret.append([leftfact, rightfact])
		
		return ret
	
	def OuterElements(self):
		retdict = {p:[] for p in self.poset}
		for p in self.poset:
			psupp = [i for (i,a) in enumerate(self.atoms) if self.poset.covers((p - a) % self.m, p)]
			for (i,a) in enumerate(self.atoms):
				if self.poset.covers(p, (p + a) % self.m):
					continue
				
				# verify the resulting factorizations will actually live in an outer Betti element
				if any(not self.poset.covers((p - self.atoms[j]) % self.m, (p - self.atoms[j] + a) % self.m) for j in psupp):
					continue

				newbetti = []
				for fact in self.Factorization(p):
					fact2 = list(fact)
					fact2[i] = fact2[i] + 1
					newbetti.append(tuple(fact2))

				retdict[(p + a) % self.m].append(newbetti)
		
		for retp in retdict:
			ret = retdict[retp]
			# merge connected factorization sets
			for j in reversed(range(len(ret))):
				for k in reversed(range(j)):
					if any([f in ret[j] for f in ret[k]]):
						ret[k] = list(set(ret[k] + ret[j]))
						del ret[j]
						break
			
			retdict[retp] = ret
		
		return sum(retdict.values(), [])
	
	def OuterBettiElements(self):
		ret = self.OuterElements()
		# check for legit outer betti
		for j in reversed(range(len(ret))):
			retp = sum(a*b for (a,b) in zip(ret[j][0],self.atoms))
			supp = list(set([i for fact in ret[j] for (i,f) in enumerate(fact) if f != 0]))
			flag = False

			for i in supp:
				elem = (retp - self.atoms[i]) % self.m

				bettiless = []
				for fact in ret[j]:
					if fact[i] == 0:
						continue

					fact2 = list(fact)
					fact2[i] = fact2[i] - 1
					bettiless.append(tuple(fact2))

				if set(bettiless) != set([tuple(fact) for fact in self.Factorization(elem)]):
					del ret[j]
					break

		return ret
	
	def NonGeoFaceDrop(self, obfact):
		facts = {p:set([tuple(fact) for fact in self.Factorization(p)]) for p in range(self.m)}
		p = sum(a*b for (a,b) in zip(obfact,self.atoms)) % self.m
		
		if p == 0:
			return None
		
		# print(p, obfact)
		
		facts[p] = facts[p] | set([tuple(obfact)])
		
		linext = self.poset.linear_extension()
		
		while True:
			covers = [((el-self.atoms[i]) % self.m, el) for el in linext for i in range(len(self.atoms)) if any(fact[i] > 0 for fact in facts[el])]
			# print(covers)
			
			graph = DiGraph(covers)
			if not graph.is_directed_acyclic():
				return None
			
			pos = FinitePoset(graph)
			linext = pos.linear_extension()
			
			newfacts = {el:set([]) for el in linext}
			newfacts[0] = facts[0]
			
			for el in linext[1:]:
				for i in range(len(self.atoms)):
					bel = (el - self.atoms[i]) % self.m
					if not pos.covers(bel,el):
						continue
					
					adds = []
					for fact in newfacts[bel]:
						toadd = list(fact)
						toadd[i] = toadd[i] + 1
						adds.append(tuple(toadd))
					
					newfacts[el] = newfacts[el] | set(adds)
			
			for el in reversed(linext[1:]):
				for i in range(len(self.atoms)):
					bel = (el - self.atoms[i]) % self.m
					if not pos.covers(bel,el):
						continue
					
					adds = []
					for fact in newfacts[el]:
						if fact[i] == 0:
							continue
						toadd = list(fact)
						toadd[i] = toadd[i] - 1
						adds.append(tuple(toadd))
					
					newfacts[bel] = newfacts[bel] | set(adds)
			
			if newfacts == facts:
				break
			
			facts = newfacts
			# print(facts)
		
		# this automatically prunes any atoms that were lost
		return KunzPoset(poset=pos)
	
	def NonGeoFacets(self):
		ret = {}
		posets = set([])
		
		for ob in self.OuterBettiElements():
			pos = self.NonGeoFaceDrop(ob[0])
			if pos is None:
				continue
			
			if pos.Dimension() == self.Dimension()-1 and pos.poset not in posets:
				ret[ob[0]] = pos
				posets.add(pos.poset)
		
		return ret
	
	def HasFace(self):
		return self.Dimension() == self.FanFace().dim()
	
	def Orbit(self):
		m = self.m
		posets = [self.poset.relabel({i:(i*u)%m for i in range(m)}) for u in range(1,m) if gcd(u,m) == 1]
		posets = list(set(posets))
		return [KunzPoset(poset=P) for P in posets]
	
	def HasNumericalSemigroups(self):
		mpvecs = [[a-b for (a,b) in zip(rel[0], rel[1])] for rel in self.MinimalPresentation()]
		if len(mpvecs) == 0:
			return True
		
		T = ToricLattice(len(mpvecs[0]))
		L = T.submodule(mpvecs)
		
		return all(sum([a*b for (a,b) in zip(self.atoms, v)]) % self.m == 0 for v in L.saturation().basis())
	
	def LocateNumericalSemigroup(self, minimize_genus = True):
		m = self.m
		atoms = self.atoms
		
		if not self.HasNumericalSemigroups():
			return None
		
		blp = MixedIntegerLinearProgram(maximization=False)
		z = blp.new_variable(integer=True, nonnegative=True)

		for rel in self.FullMinimalPresentation():
			if rel[1][0] == 0:
				blp.add_constraint(sum(z[i]*ri for (i,ri) in zip(atoms,rel[0][1:])) == sum(z[i]*ri for (i,ri) in zip(atoms,rel[1][1:])))
			else:
				blp.add_constraint(sum(z[i]*ri for (i,ri) in zip(atoms,rel[0][1:])) >= 1 + sum(z[i]*ri for (i,ri) in zip(atoms,rel[1][1:])))

		q = blp.new_variable(integer=True, nonnegative=True)
		for i in atoms:
			blp.add_constraint(m*(q[i]+1) + i == z[i])
		
		# if the region is not bounded, GLPK will sometimes hang
		blp.add_constraint(sum(z[i] for i in atoms) <= m^3)

		if minimize_genus:
			blp.set_objective(sum(sum(z[i]*fi for (i,fi) in zip(atoms,self.Factorization(i)[0])) for i in range(m)))
		
		# blp.show()
		solution = blp.solve()

		zvals = blp.get_values(z)
		return NumericalSemigroup([m] + [int(zvals[i]) for i in atoms])
	
	def ContainsFaceOfPoset(self, P2):
		setofhyps = set(P2.hyperplane_desc)
		return all((hyp in setofhyps) for hyp in self.hyperplane_desc)

	@staticmethod
	def KunzInequalities(m):
		return KunzPoset.__GeneralGroupConeInequalities(AbelianGroup([m]))

	@staticmethod
	def __GeneralGroupConeInequalities(G, elements=None):
		if elements == None:
			elements = sorted([a for a in G if a != G(1)])
		
		ind = {a:elements.index(a) for a in elements}
		
		ieqs = []
		for a in elements:
			for b in elements:
				if a*b not in elements or ind[a] > ind[b]:
					continue
				
				ieq = [0]*len(elements)
				ieq[ind[a]] += 1
				ieq[ind[b]] += 1
				ieq[ind[a*b]] -= 1
				ieqs.append([0] + ieq)
		
		return ieqs

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
					ineq = list(map(int, [s for s in line.split() if len(s) > 0]))
					hyperplane_list.append(ineq)
		
		return hyperplane_list

	@staticmethod
	def IterateFacesFromNormaliz(face_lattice_file_path='data.fac', hplane_file_path='data.out', faceindices=None, dimension=None):
		hyperplane_list = KunzPoset.ReadHyperplanesFromNormaliz(hplane_file_path)
		multiplicity = len(hyperplane_list[0]) + 1
		M = max(faceindices) if faceindices != None else oo
		
		# faces = []
		
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
					# faces.append(P)
					yield P
				except ValueError as e:
					if str(e) == "Hasse diagram contains cycles":
						pass
					else:
						raise
		
		# return faces
	
	@staticmethod
	def ReadFacesFromNormaliz(face_lattice_file_path='data.fac', hplane_file_path='data.out', faceindices=None, dimension=None):
		return list(KunzPoset.IterateFacesFromNormaliz(face_lattice_file_path=face_lattice_file_path, 
			hplane_file_path=hplane_file_path, faceindices=faceindices, dimension=dimension))









class KunzFan:
	def __init__(self, m, A):
		self.m = m
		self.A = list(A)
		
		self.posets = None
		self.chambers = None
		self.fullcone = None
	
	def CircleOfLights(self, V):
		m = self.m
		A = self.A
		
		atomvals = {a:v for (a,v) in zip(A,V)}
		
		cone_coordinates = [oo for i in range(m)]
		
		queue = [(0,0)]
		
		i = -1
		while i+1 < len(queue):
			i = i + 1
			
			(N,v) = queue[i]
			if cone_coordinates[N] < v:
				continue
			
			for a in A:
				(N2,v2) = ((N + a) % m, v + atomvals[a])
				if v2 < cone_coordinates[N2]:
					cone_coordinates[N2] = v2
					queue.append((N2,v2))
		
		return cone_coordinates[1:]

	def ConeForPoset(self, P):
		m = self.m
		A = self.A

		eqns = []
		ieqs = []
		for rel in P.FullMinimalPresentation():
			eq = {a:b-c for (a,b,c) in zip(P.atoms,rel[0][1:],rel[1][1:])}
			eq = [0] + [eq[a] if a in eq else 0 for a in A]

			if rel[1][0] == 0:
				eqns.append(eq)
			else:
				ieqs.append(eq)

		for a2 in A:
			if a2 not in P.atoms:
				fact = P.Factorization(a2)[0]
				eq = {a:b for (a,b) in zip(P.atoms,fact)}
				eq[a2] = -1
				eq = [0] + [eq[a] if a in eq else 0 for a in A]
				eqns.append(eq)

		return Polyhedron(eqns=eqns, ieqs=ieqs+matrix.identity(len(A)+1).rows()[1:])

	def DoKunzWalk(self, req_facts=[], compute_all_faces=False):
		m = self.m
		A = self.A

		facequeue = []
		unmatched = set([])
		
		retchambers = []
		retposets = []
		
		# build the cone in which the fan lives
		# TODO refine this process
		ieqs = []
		for i in range(len(A)):
			ranges = [list(range(m))]*len(A)
			ranges[i] = [-1]
			for ieq in itertools.product(*ranges):
				if sum(ieq) <= m - len(A) and sum([c*a for (c,a) in zip(ieq,A)]) % m == 0:
					ieqs.append((0,) + ieq)
		
		sub_facts = []
		for fact in req_facts:
			subfactranges = [list(range(fact[i]+1)) if fact[i] > 0 else [0] for i in range(len(A))]
			for subfact in itertools.product(*subfactranges):
				sub_facts.append(subfact)
		sub_facts = [subfact for subfact in set(sub_facts) if sum(subfact) > 1]
		
		usedelms = []
		for subfact in sub_facts:
			p = sum([c*a for (c,a) in zip(subfact,A)]) % m
			if p == 0 or p in A or p in usedelms:
				continue
			
			usedelms.append(p)
			
			ranges = [list(range(m)) if subfact[i] == 0 else [0] for i in range(len(A))]
			for ieq in itertools.product(*ranges):
				if sum(ieq) >= m:
					continue
				ieq2 = tuple([c1-c2 for (c1,c2) in zip(ieq,subfact)])
				if sum([c*a for (c,a) in zip(ieq2,A)]) % m == 0:
					ieqs.append((0,) + ieq2)
		
		fullcone = Polyhedron(ieqs=ieqs+matrix.identity(len(A)+1).rows()[1:])
		self.fullcone = fullcone
		
		if fullcone.dimension() < len(A):
			self.posets = retposets
			self.chambers = retchambers
			return
		
		# seed the process with a central(ish) chamber
		initpt = list(sum([vector(ray) for ray in fullcone.rays()]))
		P = KunzPoset(cone_coordinates=self.CircleOfLights(initpt))
		
		while P.Dimension() < len(A):
			randray = fullcone.rays()[random.randint(0,len(fullcone.rays())-1)]
			initpt = [v1+v2 for (v1,v2) in zip(initpt, randray)]
			P = KunzPoset(cone_coordinates=self.CircleOfLights(initpt))
		
		chamber = self.ConeForPoset(P)
		
		retposets.append(P)
		retchambers.append(chamber)
		
		for facet in chamber.facets():
			F = facet.as_polyhedron()
			
			facequeue.append((F, tuple(facet.ambient_Hrepresentation()[0][1:])))
			unmatched.add(F)
		
		# walk to new chambers until fan is complete
		curface = 0
		while curface < len(facequeue):
			(F,normvec) = facequeue[curface]
			curface = curface + 1
			
			if F not in unmatched:
				continue
			
			interiorpt = [sum([ray[i] for ray in F.rays()]) for i in range(len(A))]
			if not(fullcone.interior_contains(interiorpt)):
				unmatched.remove(F)
				continue
			
			addvec = [v/10 for v in normvec]
			P = None
			chamber = None
			facets = None
			nvecs = None
			
			while True:
				addvec = [v/10 for v in addvec]
				pt = [c-b for (c,b) in zip(interiorpt, addvec)]
				P = KunzPoset(cone_coordinates=self.CircleOfLights(pt))
				chamber = self.ConeForPoset(P)
				facets = [facet.as_polyhedron() for facet in chamber.facets()]
				nvecs = [tuple(facet.ambient_Hrepresentation()[0][1:]) for facet in chamber.facets()]
				if P.Dimension() == len(A) and F in facets:
					break
			
			retposets.append(P)
			retchambers.append(chamber)
			
			for (F2,nv2) in zip(facets, nvecs):
				if F2 in unmatched:
					unmatched.remove(F2)
				else:
					facequeue.append((F2, nv2))
					unmatched.add(F2)
		
		self.posets = retposets
		self.chambers = retchambers

		if not compute_all_faces:
			return

		pts = []
		for chamber in self.chambers:
			for d in [1..len(A)-1]:
				for F in chamber.faces(d):
					v = sum([vector(r) for r in F.rays()], vector([0]*len(A)))
					if not fullcone.interior_contains(v):
						continue
					pts.append(tuple(v))
		
		pts = list(set(pts))
		for v in pts:
			P = KunzPoset(cone_coordinates=self.CircleOfLights(v))
			self.posets.append(P)


	def Plot(self):
		if self.chambers == None or len(self.chambers) == 0:
			print("You must walk first!")
			return

		chambers = self.chambers

		def theproj(v):
			v = vector(v) - vector([sum(v)/3]*3)
			mat = matrix([
				[ 1/3, 1/3, 1/3],
				[ 1/3,-1/3, 1/3],
				[-2/3, 0/3, 1/3],
				# [-1/2, 1/2, 1/2, 1/2],
				# [ 1/2,-1/2, 1/2, 1/2],
				# [ 1/2, 1/2,-1/2, 1/2],
				# [-1/2,-1/2,-1/2, 1/2],
			]).inverse()
			return (mat*v)[:2]

		if self.fullcone.dimension() == 2:
			box = Polyhedron(ieqs=[[0,1,0], [0,0,1], [10,-1,-1]])
			pl = chambers[0].intersection(box).plot()
			for C in chambers:
				pl = pl + C.intersection(box).plot()
			return pl

		if self.fullcone.dimension() == 3:
			hyp = Polyhedron(eqns=[[-1,1,1,1]])
			verts = []
			edges = []

			for C in chambers:
				P = C.intersection(hyp)
				for v in P.vertices():
					verts.append(tuple(theproj(v)))
				for ed in P.faces(1):
					edges.append(tuple([theproj(v) for v in ed.vertices()]))

			pl = points(verts, size=30, color='black', axes=False)

			for ed in edges:
				pl = pl + line(ed, thickness=0.5, color='black', axes=False)

			pl = pl + points(verts, size=30, color='black', axes=False)

			# pl.show(viewer='threejs', online=True)
			return pl

	@staticmethod
	def IterateAtomSets(m, e):
		posetlist = set([])
		for A in itertools.combinations([1..m-1], e-1):
			if gcd(A + (m,)) > 1:
				continue

			A2 = min([tuple(sorted([(u*a)%m for a in A])) for u in [1..m-1] if gcd(u,m) == 1])
			if A2 in posetlist:
				continue

			posetlist.add(A2)
			yield A2

	@staticmethod
	def IterateKunzPosets(m, e, t=None, eta=None):
		for A in KunzFan.IterateAtomSets(m,e):
			KW = KunzFan(m,A)
			KW.DoKunzWalk(compute_all_faces=True)
			for P in KW.posets:
				if t != None and len(P.poset.maximal_elements()) != t:
					continue

				if eta != None and len(P.FullMinimalPresentation()) != eta:
					continue

				yield P



	# # old implementation
	# def __OuterBettiFactorizationSets(self):
	# 	ret = []
	# 	for p in self.poset:
	# 		for (i,a) in enumerate(self.atoms):
	# 			if self.poset.covers(p, (p + a) % self.m):
	# 				continue

	# 			newbetti = []
	# 			for fact in self.Factorization(p):
	# 				fact2 = list(fact)
	# 				fact2[i] = fact2[i] + 1
	# 				newbetti.append(tuple(fact2))

	# 			ret.append(newbetti)

	# 	# merge connected factorization sets
	# 	for j in reversed(range(len(ret))):
	# 		for k in reversed(range(j)):
	# 			if any([f in ret[j] for f in ret[k]]):
	# 				ret[k] = list(set(ret[k] + ret[j]))
	# 				del ret[j]
	# 				break
		
	# 	# check for legit outer betti
	# 	for j in reversed(range(len(ret))):
	# 		supp = list(set([i for fact in ret[j] for (i,f) in enumerate(fact) if f != 0]))
	# 		flag = False

	# 		for i in supp:
	# 			elem = (sum([self.atoms[k]*f for (k,f) in enumerate(ret[j][0])]) - self.atoms[i]) % self.m

	# 			bettiless = []
	# 			for fact in ret[j]:
	# 				if fact[i] == 0:
	# 					continue

	# 				fact2 = list(fact)
	# 				fact2[i] = fact2[i] - 1
	# 				bettiless.append(tuple(fact2))

	# 			if set(bettiless) != set([tuple(fact) for fact in self.Factorization(elem)]):
	# 				del ret[j]
	# 				break

	# 	return ret
	
	# # attempted without using factorizations, 
	# # only medium confidence of correrctness
	# def __OuterBettiSupports(self):
	# 	psupps = {p:[] for p in self.poset}
	# 	ins = {p:[] for p in self.poset}
	# 	ret = []
		
	# 	# build in sets
	# 	for p in self.poset:
	# 		psupps[p] = [i for (i,a) in enumerate(self.atoms) if self.poset.covers((p - a) % self.m, p)]
			
	# 		for (i,a) in enumerate(self.atoms):
	# 			if self.poset.covers(p, (p + a) % self.m):
	# 				continue
				
	# 			# verify the resulting factorizations will actually live in an outer Betti element
	# 			if any(not self.poset.covers((p - self.atoms[j]) % self.m, (p - self.atoms[j] + a) % self.m) for j in psupps[p]):
	# 				continue

	# 			ins[(p + a) % self.m].append(i)
		
	# 	for p in self.poset:
	# 		# build support set connected components
	# 		supps = [list(set(psupps[(p - self.atoms[i]) % self.m] + [i])) for i in ins[p]]
	# 		for j in reversed(range(len(supps))):
	# 			for k in reversed(range(j)):
	# 				if any(i in supps[j] for i in supps[k]):
	# 					supps[k] = list(set(supps[k] + supps[j]))
	# 					del supps[j]
	# 					break
			
	# 		ret = ret + [(p,supp) for supp in supps if all(i in ins[p] for i in supp)]
		
	# 	# build actual outer bettis
	# 	for j in range(len(ret)):
	# 		(p,supp) = ret[j]
			
	# 		outerbetti = []
	# 		for i in supp:
	# 			for fact in self.Factorization((p - self.atoms[i]) % self.m):
	# 				fact2 = list(fact)
	# 				fact2[i] = fact2[i] + 1
	# 				outerbetti.append(tuple(fact2))
			
	# 		ret[j] = list(set(outerbetti))
		
	# 	return ret
	
	# def __outerelementinfo(self, upper_factorizations):
	# 	# TODO: build poset too
	# 	factlistsbyfacts = {}
	# 	outerposetelements = []
	# 	outerposetcoverrelations = []
	# 	minpreselements = []
	# 	outerminrelations = []
	# 	allfacts = queue.Queue()
	# 	minpreschecks = []
		
	# 	for p in self.poset.linear_extension():
	# 		factlist = [list(sorted([tuple(f) for f in self.Factorization(p)])), []]
	# 		outerposetelements.append(factlist)
			
	# 		for f in factlist[0]:
	# 			factlistsbyfacts[tuple(f)] = len(outerposetelements) - 1
	# 			for i in range(len(f)):
	# 				f2 = list(f)
	# 				f2[i] = f2[i] + 1
	# 				allfacts.put(tuple(f2))
	# 				minpreschecks.append(tuple(f2))
		
	# 	upperfacts = set([tuple(f) for f in upper_factorizations if tuple(f) not in factlistsbyfacts])
		
	# 	def parsenext(f):
	# 		factlist = [[f], []]
	# 		nextcovers = []
	# 		gensbacked = []
	# 		runagain = True
			
	# 		while runagain:
	# 			runagain = False
	# 			for i in range(len(f)):
	# 				if i in gensbacked:
	# 					continue
					
	# 				for ff in factlist[0]:
	# 					if ff[i] > 0:
	# 						break
					
	# 				if ff[i] == 0:
	# 					continue
					
	# 				runagain = True
	# 				gensbacked = gensbacked + [i]
					
	# 				backone = list(ff)
	# 				backone[i] = backone[i] - 1
					
	# 				if tuple(backone) not in factlistsbyfacts:
	# 					return ([],[])
					
	# 				cover = factlistsbyfacts[tuple(backone)]
	# 				nextcovers.append(cover)
					
	# 				for j in [0,1]:
	# 					for ff2 in outerposetelements[cover][j]:
	# 						ff3 = list(ff2)
	# 						ff3[i] = ff3[i] + 1
							
	# 						factlist[j].append(tuple(ff3))
			
	# 		factlist[0] = list(set(factlist[0]))
	# 		factlist[1] = list(set(factlist[1]))
			
	# 		if len(factlist[1]) == 0:
	# 			elem = sum([a*fi for (a,fi) in zip(self.atoms,f)]) % self.m
	# 			if list(f) not in self.Factorization(elem):
	# 				factlist[1] = factlist[1] + [tuple(f2) for f2 in self.Factorization(elem)]
			
	# 		return (factlist, nextcovers)
		
	# 	# compute full minimal presentation first, otherwise order gets messed up
	# 	minpresouterelements = []
	# 	minpresfacts = {}
	# 	for f in minpreschecks:
	# 		if f in factlistsbyfacts or f in minpresfacts:
	# 			continue
			
	# 		(factlist, nextcovers) = parsenext(f)
			
	# 		if factlist == []:
	# 			continue
			
	# 		for ff in factlist[0]:
	# 			minpresfacts[ff] = True
	# 		minpresouterelements.append((factlist, nextcovers))
	# 		# don't update factlistsbyfacts yet!
		
	# 	# do Betti matrix merging
	# 	for (factlist, nextcovers) in minpresouterelements:
	# 		newindex = len(outerposetelements)
	# 		for elem in minpreselements:
	# 			leftfact = outerposetelements[elem][0][0]
	# 			rightfact = factlist[0][0]
	# 			thevec = vector([a-b for (a,b) in zip(leftfact, rightfact)])
	# 			try:
	# 				self.BettiMatrix().solve_left(thevec)
	# 			except ValueError as e:
	# 				continue
				
	# 			newindex = elem
	# 			break
			
	# 		# actually new
	# 		if newindex == len(outerposetelements):
	# 			# redundant but better than missing some
	# 			outerposetelements.append([[],factlist[1]])
	# 			minpreselements.append(newindex)
				
	# 			outerposetcoverrelations = outerposetcoverrelations + [(c, newindex) for c in nextcovers]
				
	# 			f = factlist[0][0]
	# 			# add next things to try
	# 			for i in range(len(f)):
	# 				f2 = list(f)
	# 				f2[i] = f2[i] + 1
	# 				allfacts.put(tuple(f2))
			
	# 		if factlist[0][0] in outerposetelements[newindex][0]:
	# 			continue
			
	# 		for ff in factlist[0]:
	# 			outerposetelements[newindex][0].append(ff)
	# 			factlistsbyfacts[ff] = newindex
	# 			if ff in upperfacts:
	# 				upperfacts.remove(ff)
		
	# 	# now compute the higher ones
	# 	while len(upperfacts) > 0:
	# 		f = allfacts.get()
			
	# 		if f in factlistsbyfacts:
	# 			continue
			
	# 		(factlist, nextcovers) = parsenext(f)
			
	# 		if factlist == []:
	# 			continue
			
	# 		newindex = len(outerposetelements)
	# 		# isnew = True
	# 		# isminpres = False
			
	# 		# # indicates this has a minmal relation
	# 		# if all(cover < self.m for cover in nextcovers):
	# 		#     isminpres = True
	# 		#     outerminrelations.append([[0] + list(factlist[0][0]), [1] + list(factlist[1][0])])
	# 		#     for elem in minpreselements:
	# 		#         leftfact = outerposetelements[elem][0][0]
	# 		#         rightfact = factlist[0][0]
	# 		#         thevec = vector([a-b for (a,b) in zip(leftfact, rightfact)])
	# 		#         try:
	# 		#             self.BettiMatrix().solve_left(thevec)
	# 		#         except ValueError as e:
	# 		#             continue
					
	# 		#         # these are secretly the same element
	# 		#         isnew = False
	# 		#         newindex = elem
	# 		#         outerposetelements[elem][0] = outerposetelements[elem][0] + factlist[0]
	# 		#         break
			
	# 		# if isnew:
	# 		#     outerposetelements.append(factlist)
			
	# 		# if isnew and isminpres:
	# 		#     minpreselements.append(newindex)
			
	# 		outerposetelements.append(factlist)
			
	# 		outerposetcoverrelations = outerposetcoverrelations + [(c, newindex) for c in nextcovers]
	# 		for ff in factlist[0]:
	# 			factlistsbyfacts[ff] = newindex
	# 			if ff in upperfacts:
	# 				upperfacts.remove(ff)
			
	# 		# add next things to try
	# 		for i in range(len(f)):
	# 			f2 = list(f)
	# 			f2[i] = f2[i] + 1
	# 			allfacts.put(tuple(f2))
		
	# 	for (op,factlist) in enumerate(outerposetelements):
	# 		unifiedfacts = [(0,) + ff for ff in factlist[0]]
	# 		unifiedfacts = unifiedfacts + [(1,) + ff for ff in factlist[1]]
	# 		outerposetelements[op] = unifiedfacts
		
	# 	outerposet = Poset((list(range(len(outerposetelements))), outerposetcoverrelations), cover_relations=True)
		
	# 	return (outerposet, outerposetelements, minpreselements, outerminrelations)
	
	# def __OuterElementPoset(self, upper_factorizations = None):
	# 	if upper_factorizations is None:
	# 		upper_factorizations = [tuple([fi+1 for fi in f]) for p in self.poset.maximal_elements() for f in self.Factorization(p)]
		
	# 	(outerposet, outerposetelements, outerminpreselements, outerminrelations) = self.__outerelementinfo(upper_factorizations)
		
	# 	return (outerposet, outerposetelements)
	
	# def __FullMinimalPresentation(self, kunz_coords = None):
	# 	upper_factorizations = [tuple([(fi+1 if i == j else fi) for (i,fi) in enumerate(self.Factorization(p)[0])]) for p in self.poset.maximal_elements() for j in range(len(self.atoms))]
		
	# 	(outerposet, outerposetelements, outerminpreselements, outerminrelations) = self.__outerelementinfo(upper_factorizations)
		
	# 	ret = [[[0] + p1, [0] + p2] for [p1,p2] in self.MinimalPresentation()]
		
	# 	for [leftfact, rightfact] in outerminrelations:
	# 		if kunz_coords is not None:
	# 			rightfact[0] = sum([(b-c)*kunz_coords[a2-1] for (a2,b,c) in zip(self.atoms, leftfact[1:], rightfact[1:])])
	# 			rightfact[0] = rightfact[0] + sum([(b-c)*a2 for (a2,b,c) in zip([0]+self.atoms, leftfact, rightfact)])/self.m
			
	# 		ret.append([leftfact, rightfact])
		
	# 	return ret
	
	# def __OuterBettiFactorizationSets(self):
	# 	upper_factorizations = [tuple([fi+1 for fi in f]) for p in self.poset.maximal_elements() for f in self.Factorization(p)]
		
	# 	(outerposet, outerfacts, outerminpreselements, outerminrelations) = self.__outerelementinfo(upper_factorizations)
		
	# 	ret = {d:[] for d in range(len(self.atoms))}
	# 	for op in outerposet:
	# 		factlist = outerfacts[op]
	# 		sdc = SimplicialComplex(maximal_faces=[[i for i in range(len(f)) if f[i] > 0] for f in factlist], maximality_check=True)
	# 		hom = sdc.homology()
	# 		for d in range(len(hom)):
	# 			if len(hom[d].gens()) > 0:
	# 				ret[d] = ret[d] + [factlist]*len(hom[d].gens())
		
	# 	return ret
	
	# def __OuterBettiElements(self):
	# 	outerbettifacts = self.OuterBettiFactorizationSets()
	# 	return {d:list(sorted([sum([a*b for (a,b) in zip([0]+self.atoms,factlist[0])])%self.m for factlist in outerbettifacts[d]])) for d in range(len(self.atoms))}
	
	# def _FindSemigroupsOld(self, max_kunz_coord, how_many, min_kunz_coord = 2):
	# 	poset = self.poset
	# 	trucks = []
	# 	modulus_fails = 0
	# 	total_attempts = 0
		
	# 	if self.Dimension() == len(atoms):
	# 		while len(trucks) < how_many:
	# 			total_attempts = total_attempts + 1
	# 			temp_gens = [m]
	# 			for ii in atoms:
	# 				noop= random.randint(min_kunz_coord , max_kunz_coord)*m + ii
	# 				temp_gens.append(noop)
	# 			if not sorted([y%m for y in temp_gens]) == sorted([0] + atoms):
	# 				modulus_fails = modulus_fails + 1
	# 				if modulus_fails >= 1000 and modulus_fails == total_attempts:
	# 					print("Likely contains no semigroups")
	# 					return []
	# 				continue
					
	# 			if gcd(temp_gens) == 1:
	# 				kpp = KunzPoset(m, semigroup_gens=temp_gens).poset
	# 				if kpp == poset:
	# 					trucks.append(temp_gens)
	# 	else:
	# 		pres = matrix(QQ, self.BettiMatrix())
	# 		pres.echelonize()
	# 		while len(trucks) < how_many:
	# 			total_attempts = total_attempts + 1
	# 			temp = [0]*len(atoms)
	# 			temp_gens = [m]
	# 			for i in pres.nonpivots():
	# 				boop = random.randint(min_kunz_coord , max_kunz_coord)*m + atoms[i]
	# 				temp[i] = boop
	# 				temp_gens.append(int(boop))
	# 			vec = vector(temp)
	# 			othervars = pres*vec
	# 			# print(othervars)
	# 			for jj in othervars: 
	# 				temp_gens.append(int(-1*jj))
	# 			# print(temp_gens)
	# 			if list(sorted([y%m for y in temp_gens])) != list(sorted([0] + atoms)):
	# 				modulus_fails = modulus_fails + 1
	# 				if modulus_fails >= 10000 and modulus_fails == total_attempts:
	# 					print("Likely contains no semigroups")
	# 					return []
	# 				continue
	# 			if gcd(temp_gens) == 1 and all(x>0 for x in temp_gens):
	# 				kpp = KunzPoset(m, semigroup_gens=temp_gens).poset
	# 				#kpp.show()
	# 				if kpp == poset:
	# 					trucks.append(temp_gens)
	# 				else:
	# 					continue
	# 			else:
	# 				continue
	# 	return trucks
	

