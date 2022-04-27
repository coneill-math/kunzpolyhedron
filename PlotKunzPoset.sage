#!/usr/bin/env python
# coding: utf-8


## included this for my own personal convenience. probably want to not include in final package as they may need to use
## a different file path to load the NumericalSemigroup package
# load('/home/sage/NumericalSemigroup.sage')
from sage.plot.primitive import GraphicPrimitive


def KunzPolyEqn(mult):
	'''
	Gets the defining functions of the Kunz Polyhedron corresponding to multiplicity mult.
	
	mult: the multiplicty for the Kunz Polyhedron
	return: return the list of inequalities corresponding the Kunz polyhedron of multiplicity mult
	'''
	indexes=[1..mult-1]
	eqns=[]
	count=0 #this count avoids repetition when going over the indexes used to define the inequalities
	for jj in indexes:
		for kk in [count..mult-2]:
			if jj+indexes[kk]<mult: #handles case for no constant term
				eqn=[]
				eqn.append(0)
				#####since this is the case where the indexes are less than the multiplicity this can probably be handled
				#####more easily by using their sum as an index instead of having another for loop. can implement this
				#####in a future version
				for mm in [1..mult-1]:
					if mm==jj or mm==indexes[kk]:
						if jj==indexes[kk]:
							eqn.append(2)
						else:
							eqn.append(1)
					elif mm==jj+indexes[kk]:
						eqn.append(-1)
					else:
						eqn.append(0)
				eqns.append(eqn)
			elif jj+indexes[kk]>mult: #case for when +1 is part of inequality
				eqn=[]
				eqn.append(1)
				#####as noted above, can improve in future version by implementing a work around to avoid additional loop
				for mm in [1..mult-1]:
					if mm==jj or mm==indexes[kk]:
						if jj==indexes[kk]:
							eqn.append(2)
						else:
							eqn.append(1)
					elif mm==jj+indexes[kk]-mult:
						eqn.append(-1)
					else:
						eqn.append(0)
				eqns.append(eqn)
		count+=1
	
	#returning the eqns in this form allows them to be used as is for a polyhedron object in sage defined by inequalities
	return eqns


def FactorizeCoordinates(element,gens,chains,mult):
	'''
	Creates the list of factorizations for a given element in a poset in terms of the non-trivial minimal generators of the poset.
	
	element: the element of the poset being factorized
	gens: the list of non-trivial minimal generators of the poset
	chains: the list of maximum chains for the element of the poset
	mult: the multiplicity for the poset
	return: a list of factorizations
	'''
	factors=[]
	for cc in chains:
		if element in cc:
			factor=[0]*(len(gens)+1)
			count=cc.index(element) #finds the index of the element being factored in a particular maximal chain
			
			#iterates backwards over the maximal chain starting with the element being factored to find the difference between
			#each cover relation in the chain that determines the factorization
			while count>0:
				#based off the cover relation for a link in the chain increments the corresponding gen by 1
				factor[gens.index((cc[count]-cc[count-1])%mult)+1]+=1
				count+=-1
			factor[gens.index(cc[count])+1]+=1
			
			#prevents adding the same factorization multiple times as there may be multiple chains that give same factorization
			if factor not in factors:
				factors.append(factor)
	return factors


def RayCoordinates(mult,gens,chains,verbose=False,vector_directions=None):
	'''
	Gets the coordinates for where to place each element in the poset based of the factorization
	
	mult: the multiplicity corresponding to the Kunz polyhedron where the poset lives
	gens: the list of non-trivial minimum generators
	chains: the list of maximal chains for each element in the poset
	verbose: an optional parameter that when set to True adds additional print statements. defaulted to False. mostly used for debugging
    vector_directions: an optional parameter that gives the arrow directions and magnitude corresponding to each minimal generator
	return: returns a dictionary of coordiantes for each element in the poset
	'''
	coord=[0..mult-1]
	leng=len(gens)
	assert CheckVectorDirections(leng,vector_directions), "Invalid parameter setup for 'vector_directions'"
	
	#whether to include the factorization for zero in the dictionary of factorizations, currently implemented, may not be needed
	factorizationZero=[0]*(leng+1)
	dict1={0:[factorizationZero]}
	#dict1={}
	
	for ii in coord[1:]:
		factors=FactorizeCoordinates(ii,gens,chains,mult) #gets the list of factorizations for a particular element
		if verbose:
			print('factorizations of '+str(ii)+': '+str(factors))
		length=len(factors)*1.0
		
		#checks if the individual element is graded by counting the number of factors in each factorization and checking for uniqueness
		gradedCheck=True
		lengthCheck=sum(factors[0])
		for fact in factors[1:]:
			if sum(fact)!=lengthCheck:
				gradedCheck=False
				
		#if the element is graded uses the first factorization in the list to determine the elements placement in the poset
		#####better way to do this? take into account each possible factorization if not unique?
		if gradedCheck:
			dict1[int(ii)]=factors
			
		#if the element is not graded determines its position based off the average of the factorization for where to horizontally place the element
		#determines the vertically placement based off the maximum height needed to be achieved to make sure every edge goes up
		else:
			averageFact=(int(leng)+1)*[0]
			maxHeight=0
			for mm in factors:
				testMax=sum(mm)
				if testMax>maxHeight:
					maxHeight=testMax
				for nn in [0..leng]:
					averageFact[int(nn)]+=mm[int(nn)]*1.0
			for ll in [0..leng]:
				averageFact[int(ll)]=(averageFact[int(ll)]*1.0)/(length*1.0)
			averageFact.append(maxHeight)
			dict1[int(ii)]=[tuple(averageFact)]
	if verbose:
		print('average factorizations of elements: '+str(dict1))
	
	
	#generates the list of vector directions for the non-trivial minimum generators to base the poset design
	##### add implementation for shift like in NSG_Poset?
	if vector_directions is None:
		dict2={0:(0,0)}    
		if leng%2==0:
			for mm in [1..leng/2]:
				dict2[mm]=(((-1*((leng)/2-mm+0.5))),1.0)
			for nn in [leng/2+1..leng]:
				dict2[nn]=(nn-leng/2-0.5,1.0)
		else:
			for mm in [1..(leng-1)/2]:
				dict2[mm]=((-1*((leng-1)/2-mm+1)),1.0)
			for nn in [(leng+1)/2+1..leng]:
				dict2[nn]=(nn-(leng+1)/2,1.0)
			dict2[(leng+1)/2]=(0.0,1.0)
	else:
		dict2=vector_directions
	if verbose:
		print('direction of generators: '+str(dict2))
	
	#determines where to place each element in the poset from the average factorization of each element as well as the vector directions of non-trivial minimum generators
	coords={0:(0,0)}
	for jj in coord[1:]:
		count=0
		factor=dict1[jj][0]
		coordinate=[0,0]
		flag=False
		if len(factor)==(leng+1):
			for kk in factor:
				if kk!=0:
					coordinate[0]+=dict2[count][0]*kk
					coordinate[1]+=dict2[count][1]*kk
				count+=1
				if kk%1!=0:
					flag=True
			if flag:
				coordinate[0]+=0.25
		else:
			for kk in factor[:len(factor)-1]:
				if kk!=0:
					coordinate[0]+=dict2[count][0]*kk
				count+=1
				if kk%1!=0:
					flag=True
			if flag:
				coordinate[0]+=0.25
			coordinate[1]=factor[len(factor)-1]-0.5
		coords[jj]=tuple(coordinate)

	#checks over the coordinates for each element to make sure nothing overlaps
	#####consider implementing multiple iterations to make sure no elements end up overlapping after the iteration?
	for mm in coord:
		for nn in coord:
			if mm!=nn:
				if coords[mm]==coords[nn]:
					tempCoord1=list(coords[mm])
					tempCoord2=list(coords[nn])
					tempCoord1[0]+=-0.2
					tempCoord2[0]+=0.2
					coords[mm]=tuple(tempCoord1)
					coords[nn]=tuple(tempCoord2)
	
	if verbose:
		print('coordinates of elements in poset: '+str(coords))
	return coords


def RayEquations(ray,count,verbose=False):
	'''
	Generates the inequalities of the Kunz polyhedron that a particular ray satisfies with equality.
	
	ray: a list giving the vector direction of the ray that is getting the equations for
	count: for the list of rays inputed to function RaysPoset, counts which ray in the list it is
	verbose: an optional parameter that when set to True adds additional print statements. defaulted to False. mostly used for debugging
	return: a list of representing the defining inequalities of the Kunz polyhedron satisfied with equality for the ray
	'''
	mult=len(ray) #the dimension corresponding to the Kunz polyhedron that the ray lives in
	ieqn=KunzPolyEqn(mult+1) #gets the list of definining inequalities for the Kunz polyhedron
	if verbose and count==1:
		print('Defining Inequalities of Kunz Polyhedra: '+str(ieqn))
		
	#creates a list for the vertex of the Kunz polyhedron
	vtx=[]
	for ii in [1..mult]:
		vtx.append((-1*ii)/(mult+1))
	
	#generates a list of points based off the vertex of the Kunz polyhedron and the vector direction of the ray
	pt=[]
	for jj in [0..mult-1]:
		pt.append(vtx[jj]+ray[jj])
	
	#checks for each of the defining inequalities of the Kunz polyhedron, which are satisfied by equality for the ray
	eqn=[]
	for mm in ieqn:
		total=mm[0]
		for nn in [1..mult]:
			total+=mm[nn]*pt[nn-1]
		if total==0:
			eqn.append(mm)
			
	#####consider just using the vector direction to increase efficiency of program by ignoring the constant term of the
	#####defining inequalities of the Kunz polyhedron
	
	if verbose:
		print('equations satisifying equality of ray '+str(count)+': '+str(eqn))
	
	return eqn


def RaysPoset(rays,fsize=10,colored=True,verbose=False,vector_directions=None):
	'''
	Creates the Poset given the bounding rays of a Kunz Polyhedra.
	If the list of rays inputted do not define a face or are not the full list of extremal rays for the face, may not generate the correct poset
	
	rays: a list of rays as vector direction for which a poset is being generated
	fsize: an optional parameter for the size of the graphic of the poset to be plotted. defaulted at 10
	colored: an optional parameter to determine if the poset should have colored edges. defaulted to True
	verbose: an optional parameter that when set to True adds additional print statements. defaulted to False. mostly used for debugging
    vector_directions: an optional parameter that gives the arrow directions and magnitude corresponding to each minimal generator
	return: a graphic object of the poset corresponding to the face bounded by the list of rays inputted
	'''
	
	#checks if the list of rays inputted all came from the same dimension
	lengthCheck=len(rays[0])
	for rrr in rays[1:]:
		if len(rrr)!=lengthCheck:
			return 'All Rays Must Be From The Same Dimension'
		
	#checks if the list of rays all correspond to a lower dimension Kunz Polyhedron
	#ex: if inputted rays were [1,2,0,1,2] and [2,1,0,2,1]
	commonzeros=[]
	for aa in [0..len(rays[0])-1]:
		coords=[ray[aa] for ray in rays]
		if Set(coords)=={0}:
			commonzeros.append(aa)
			
	#generates the list of equations satisified by equality for all the rays inputted
	count=1
	if len(commonzeros)>0: #handles the case where the rays correspond to a poset in a lower dimension
		flag=True
		m=commonzeros[0]
		permEqn=RayEquations(rays[0][0:m],count,verbose)
		for rr in rays[1:]:
			count+=1
			tempEqn=RayEquations(rr[0:m],count,verbose)
			permEqn=[eqn for eqn in permEqn if eqn in tempEqn]
		if verbose:
			print('common zeros in indices: '+str(commonzeros))
	else: #handles the case if the rays correspond to a poset for the dimesnion they live in
		flag=False
		m=len(rays[0])
		permEqn=RayEquations(rays[0],count,verbose)
		for rr in rays[1:]:
			count+=1
			tempEqn=RayEquations(rr,count,verbose)
			permEqn=[eqn for eqn in permEqn if eqn in tempEqn]
	if verbose:
		print('eqns: ' + str(permEqn))
		
	#generates the list of relations for the entire poset based off the equations satisfied with equality
	covers=[]
	for ii in permEqn:
		pos=[]
		for jj in [1..len(ii)-1]:
			temp = ii[jj]
			if temp>0:
				pos.append(jj)
			if temp<0:
				neg=jj
		for kk in pos:
			covers.append([kk,neg])
	if verbose:
		print('general relations: '+str(covers))
		
	#finds the list of non-trivial minimal generators for the poset based off which elements do not cover any other element (excluding zero)
	gens=[1..m]
	for cc in covers:
		if cc[1] in gens:
			gens.remove(cc[1])
			
	#for the list of relations between elements, finds which are cover relations due to their difference being a generator
	realcovers=[]
	if verbose:
		print('gens: '+str(gens))
	for dd in covers:
		if ((dd[1]-dd[0])%(m+1)) in gens:
			realcovers.append((dd[0],dd[1]))
			
	#creates the list of elements in the poset as well as the list of cover relations
	comb=2*[0]
	comb[0]=[1..m]
	comb[1]=realcovers
	if verbose:
		print('cover relations: '+str(comb[1]))
		
	#generates a poset using the default sage method for posets
	PP= Poset(comb, cover_relations = True)
	
	#gets the coordinate of where to place each element in the poset based off their factorization
	cords=RayCoordinates(m+1,sorted(PP.minimal_elements()),sorted(list(PP.maximal_chains())),verbose,vector_directions)
	
	#recreates the poset to include 0
	for gg in PP.minimal_elements():
		realcovers.append([0,gg])
	PP=Poset(comb,cover_relations=True)
	
	#turns the poset into a hasse diagram to customize how the elements are placed and color the edges
	HH=PP.hasse_diagram()
	
	#determines the color of each edge based off which generator the edge corresponds to
	if colored:
		colors=['red','mediumblue','forestgreen','darkmagenta','teal','orangered','olive','deeppink','gold','deepskyblue','indigo']
		count = -1
		for mm in gens:
			count += 1
			for nn in comb[1]:
				if ((nn[1]-nn[0])%(m+1))==(mm):
					HH.set_edge_label(nn[0],nn[1],count%11)
		colored={ii:colors[ii] for ii in [0..10]}
		
	#if the rays corresponds to a poset of a lower dimension than the Kunz polyhedron given, prints a message stating that fact
	if flag:
		print('poset comes from lower dimesional Kunz polyhedra due to common zeroes in rays')
	return HH.plot(pos=cords,figsize=fsize,color_by_label=colored)


def KunzPosetCoordinates(NSG,shift=False,verbose=False,vector_directions=None,show_bettis=False):
	'''
	Finds the coordinates for each vertex in a Kunz poset, used for NSG_Poset.
	
	NSG: the numerical semigroup, or a list of generators
	shift: an optional parameter for whether the minimal generators should be evenly spaced or not. defaulted to False for even spacing
	verbose: an optional parameter that when set to True adds additional print statements. defaulted to False. mostly used for debugging
    vector_directions: an optional parameter that gives the arrow directions and magnitude corresponding to each minimal generator
	return: a dictionary of tuples for where to place each element of the poset
	'''
	if type(NSG) == list:
		NSG = NumericalSemigroup(NSG)
	assert CheckVectorDirections(len(NSG.gens),vector_directions), "Invalid parameter setup for 'vector_directions'"
	gens=NSG.gens
	Ap=NSG.AperySet(min(gens)).copy() #gets the apery set for the elements in the poset
	oBettis = []
	oBettiLabels = []
	mult = min(NSG.gens)
	if show_bettis:
		bettis = NSG.BettiElements()
		iBettis = [b for ii, b in enumerate(bettis) if b in Ap]
		oBettis = [b for ii, b in enumerate(bettis) if b not in Ap]
		Ap += oBettis

		#properly name the apery set elements
		name_map = {}
		for ii, b in enumerate(oBettis):
			val = b % mult
			if val not in name_map:
				name_map[val] = 0
			else:
				name_map[val] += 1
			oBettiLabels.append(f"${val}_{{{name_map[val]}}}$")

	leng=len(gens)-1.0
	lengs=len(Ap)-1.0
	dict1={}
	NSG.FactorizationsUpToElement(max(Ap)) #factorizes all elements in the numerical semigroup up the max value of the Apery Set
	
	#finds the average factorization for each element in the Apery Set and corresponds it to its associated resiudue for the Kunz poset
	for ii in [0..lengs]:
		factorization=NSG.Factorizations(Ap[int(ii)])
		if Ap[int(ii)] in oBettis:
			#ignore factorizations that involve the multiplicity
			factorization = [f for f in factorization if f[0] == 0]
		if verbose:
			print('factorization of '+str(ii)+': '+str(factorization))
		
		#checks if a particular element of the poset is graded
		flag=True
		uniqueLength=sum(factorization[0])
		for fact in factorization[1:]:
			if sum(fact)!=uniqueLength:
				flag=False
		length=len(factorization)*1.0
		
		#if the element is graded uses the first factorization to place the element
		if flag:
			dict1[int(ii)]=factorization
		#otherwise finds the average horizontal position that would be given by all the factorizations to use
		#determines the vertically placement based off the maximum height needed to be achieved to make sure every edge goes up
		else:
			averageFact=(int(leng)+1)*[0]
			maxHeight=0
			for mm in factorization:
				testMax=sum(mm)
				if testMax>maxHeight:
					maxHeight=testMax
				for nn in [0..leng]:
					averageFact[int(nn)]+=mm[int(nn)]*1.0
			for ll in [0..leng]:
				averageFact[int(ll)]=(averageFact[int(ll)]*1.0)/(length*1.0)
			averageFact.append(maxHeight)
			dict1[int(ii)]=[tuple(averageFact)]
	if verbose:
		print('average factorizations: '+str(dict1))
	
	#finds the vector directions for each of the non-trivial minimum generators
	if vector_directions is None:
		dict2={0:(0,0)}
		if shift: #determines the vector directions so that they are not evenly spaced
			if leng%2==0:
				count=0.5
				for mm in [1..leng/2]:
					count+=mm
					dict2[mm]=dict2[mm]=((count*(-1*((leng)/2-mm+0.5))),1.0)
				for nn in [leng/2+1..leng]:
					dict2[nn]=(nn-leng/2-0.5,1.0)
			else:
				count=0.5
				for mm in [1..(leng-1)/2]:
					count+=mm
					dict2[mm]=((count*(-1*((leng-1)/2-mm+1))),1.0)
				for nn in [(leng+1)/2+1..leng]:
					dict2[nn]=(nn-(leng+1)/2,1.0)
				dict2[(leng+1)/2]=(0.0,1.0)
		else: #determines the vector direction to evenly space out the generators
			if leng%2==0:
				for mm in [1..leng/2]:
					dict2[mm]=dict2[mm]=(((-1*((leng)/2-mm+0.5))),1.0)
				for nn in [leng/2+1..leng]:
					dict2[nn]=(nn-leng/2-0.5,1.0)
			else:
				for mm in [1..(leng-1)/2]:
					dict2[mm]=((-1*((leng-1)/2-mm+1)),1.0)
				for nn in [(leng+1)/2+1..leng]:
					dict2[nn]=(nn-(leng+1)/2,1.0)
				dict2[(leng+1)/2]=(0.0,1.0)
	else:
		dict2=vector_directions
	if verbose:
		print('generator directions: '+str(dict2))

	#determines the final coordinates for each element of the poset based of the vector directions for the generators
	coord={}
	for jj in [0..lengs]:
		count=0
		factor=dict1[jj][0]
		coordinate=[0,0]
		flag=False
		#creates the coordinate for elements that are individually graded
		if len(factor)==(leng+1):
			for kk in factor:
				if kk!=0:
					coordinate[0]+=dict2[count][0]*kk
					coordinate[1]+=dict2[count][1]*kk
				count+=1
				if kk%1!=0:
					flag=True
			if flag:
				coordinate[0]+=0.25
		#creates the coordinate for if the element does not have a unique height in an ungraded poset
		else:
			for kk in factor[:len(factor)-1]:
				if kk!=0:
					coordinate[0]+=dict2[count][0]*kk
				count+=1
				if kk%1!=0:
					flag=True
			if flag:
				coordinate[0]+=0.25
			coordinate[1]=factor[len(factor)-1]-0.5
		if jj < mult:
			coord[jj]=tuple(coordinate)
		else:
			coord[oBettiLabels[int(jj)-mult]]=tuple(coordinate)
		
	#checks over the coordinates of all the elements to make sure none overlap and shift them slightly if they do
	for mm in coord:
		for nn in coord:
			if mm!=nn:
				if coord[mm]==coord[nn]:
					tempCoord1=list(coord[mm])
					tempCoord2=list(coord[nn])
					tempCoord1[0]+=-0.2
					tempCoord2[0]+=0.2
					coord[mm]=tuple(tempCoord1)
					coord[nn]=tuple(tempCoord2)
	if verbose:
		print('coordinates of elements in poset: '+str(coord))

	return coord


def AperyPosetCoordinates(NSG,shift=False,verbose=False,vector_directions=None,show_bettis=False):
	'''
	Finds the coordinates for each vertex in a Apery poset, used for NSG_Poset.
	
	NSG: the numerical semigroup, or a list of generators
	shift: an optional parameter for whether the minimal generators should be evenly spaced or not. defaulted to False for even spacing
	verbose: an optional parameter that when set to True adds additional print statements. defaulted to False. mostly used for debugging
    vector_directions: an optional parameter that gives the arrow directions and magnitude corresponding to each minimal generator
	return: a dictionary of tuples for where to place each element of the poset
	'''
	if type(NSG) == list:
		NSG = NumericalSemigroup(NSG)
	assert CheckVectorDirections(len(NSG.gens),vector_directions), "Invalid parameter setup for 'vector_directions'"
	gens=NSG.gens
	Ap=NSG.AperySet(min(gens)).copy()#gets the apery set for the elements in the poset
	oBettis = []
	if show_bettis:
		bettis = NSG.BettiElements()
		iBettis = [b for ii, b in enumerate(bettis) if b in Ap]
		oBettis = [b for ii, b in enumerate(bettis) if b not in Ap]
		Ap += oBettis
	leng=len(gens)-1.0
	lengs=len(Ap)-1.0
	dict1={}
	NSG.FactorizationsUpToElement(max(Ap))#factorizes all elements in the numerical semigroup up the max value of the Apery Set
	
	#finds the average factorization for each element in the Apery Set and corresponds it to its associated resiudue for the Kunz poset
	for ii in Ap:
		factorization=NSG.Factorizations(ii)
		if ii in oBettis:
			#ignore factorizations that involve the multiplicity
			factorization = [f for f in factorization if f[0] == 0]

		if verbose:
			print('factorization of '+str(ii)+': '+str(factorization))
			
		#checks if a particular element of the poset is graded
		flag=True
		uniqueLength=sum(factorization[0])
		for fact in factorization[1:]:
			if sum(fact)!=uniqueLength:
				flag=False
		length=len(factorization)*1.0
		
		#if the element is graded uses the first factorization to place the element
		if flag:
			dict1[ii]=factorization
		#otherwise finds the average horizontal position that would be given by all the factorizations to use
		#determines the vertically placement based off the maximum height needed to be achieved to make sure every edge goes up
		else:
			averageFact=(int(leng)+1)*[0]
			maxHeight=0
			for mm in factorization:
				testMax=sum(mm)
				if testMax>maxHeight:
					maxHeight=testMax
				for nn in [0..leng]:
					averageFact[int(nn)]+=mm[int(nn)]*1.0
			for ll in [0..leng]:
				averageFact[int(ll)]=(averageFact[int(ll)]*1.0)/(length*1.0)
			averageFact.append(maxHeight)
			dict1[int(ii)]=[tuple(averageFact)]
	if verbose:
		print('average factorizations: '+str(dict1))
	
	#finds the vector directions for each of the non-trivial minimum generators
	if vector_directions is None:
		dict2={0:(0,0)}
		if shift: #determines the vector directions so that they are not evenly spaced
			if leng%2==0:
				count=0.5
				for mm in [1..leng/2]:
					count+=mm
					dict2[mm]=dict2[mm]=((count*(-1*((leng)/2-mm+0.5))),1.0)
				for nn in [leng/2+1..leng]:
					dict2[nn]=(nn-leng/2-0.5,1.0)
			else:
				count=0.5
				for mm in [1..(leng-1)/2]:
					count+=mm
					dict2[mm]=((count*(-1*((leng-1)/2-mm+1))),1.0)
				for nn in [(leng+1)/2+1..leng]:
					dict2[nn]=(nn-(leng+1)/2,1.0)
				dict2[(leng+1)/2]=(0.0,1.0)
		else: #determines the vector direction to evenly space out the generators
			if leng%2==0:
				for mm in [1..leng/2]:
					dict2[mm]=dict2[mm]=(((-1*((leng)/2-mm+0.5))),1.0)
				for nn in [leng/2+1..leng]:
					dict2[nn]=(nn-leng/2-0.5,1.0)
			else:
				for mm in [1..(leng-1)/2]:
					dict2[mm]=((-1*((leng-1)/2-mm+1)),1.0)
				for nn in [(leng+1)/2+1..leng]:
					dict2[nn]=(nn-(leng+1)/2,1.0)
				dict2[(leng+1)/2]=(0.0,1.0)
	else:
		dict2=vector_directions
	
	#determines the final coordinates for each element of the poset based of the vector directions for the generators
	coord={}
	if verbose:
		print('generator directions: '+str(dict2))
	
	for jj in Ap:
		count=0
		factor=dict1[jj][0]
		coordinate=[0,0]
		flag=False
		#creates the coordinate for elements that are individually graded
		if len(factor)==(leng+1):
			for kk in factor:
				if kk!=0:
					coordinate[0]+=dict2[count][0]*kk
					coordinate[1]+=dict2[count][1]*kk
				count+=1
				if kk%1!=0:
					flag=True
			if flag:
				coordinate[0]+=0.25
		#creates the coordinate for if the element does not have a unique height in an ungraded poset
		else:
			for kk in factor[:len(factor)-1]:
				if kk!=0:
					coordinate[0]+=dict2[count][0]*kk
				count+=1
				if kk%1!=0:
					flag=True
			if flag:
				coordinate[0]+=0.25
			coordinate[1]+=factor[len(factor)-1]-0.5
		coord[jj]=tuple(coordinate)

	#checks over the coordinates of all the elements to make sure none overlap and shift them slightly if they do
	for mm in Ap:
		for nn in Ap:
			if mm!=nn:
				if coord[mm]==coord[nn]:
					tempCoord1=list(coord[mm])
					tempCoord2=list(coord[nn])
					tempCoord1[0]+=-0.2
					tempCoord2[0]+=0.2
					coord[mm]=tuple(tempCoord1)
					coord[nn]=tuple(tempCoord2)
	if verbose:
		print('coordinates of elements in poset: '+str(coord))

	return coord


def PlotKunzPoset(NSG,fsize=10,vsize=250,shift=False,colored=True,kunz=True,verbose=False,plot=True,vector_directions=None,show_bettis=False,partition_bettis=False):
	'''
	Creates the Kunz or Apery Poset of a Numerical Semigroup Structured by the Minimal Elements.
	
	NSG: the numerical semigroup, or a list of generators
	fsize: the size of the plot, default value of 10
	vsize: the size of the vertices, default value of 250
	shift: whether to evenly space the minimal generators and thus the rest of the poset, or to space them incrementally, default false
	colored: whether to color the edges based off the minimal element that the edge represents or not, default true
	kunz: whether to make a Kunz poset or apery poset, default is Kunz
	verbose: prints out additional information about inner workings of functions. useful for troubleshooting
    plot: whether to return a plot of the poset (graphic object) or just the poset object, default true NOTE: if returning poset object uses sage default poset style
    vector_directions: an optional parameter that gives the arrow directions and magnitude corresponding to each minimal generator
	return: a graphics type object of the plot of the poset being generated or a poset object for the numerical semigroup
	'''
	if type(NSG) == list:
		NSG = NumericalSemigroup(NSG)
	assert CheckVectorDirections(len(NSG.gens),vector_directions), "Invalid parameter setup for 'vector_directions'"
	assert show_bettis or (not partition_bettis), "Show bettis must be true to use partition_bettis"
	gens=NSG.gens
	mult=min(gens) #gets the multiplicity of the numerical semigroup
	Ap=sorted(NSG.AperySet(mult).copy()) #creates and sorts the Apery Set of the numerical semigroup
	if verbose:
		print('Apery Set (Sorted From Smallest to Largest, Not By Residue): '+str(Ap))
	
	iBettis = []
	iBettiLabels = []
	oBettis = []
	oBettiLabels = []
	#creates the Kunz poset
	if kunz:
		label_map = {}
		value_map = {}
		mult = min(NSG.gens)
		if show_bettis:
			bettis = NSG.BettiElements()
			iBettis = [b for ii, b in enumerate(bettis) if b in Ap]
			oBettis = [b for ii, b in enumerate(bettis) if b not in Ap]
			Ap += oBettis
			Ap = sorted(Ap)

			iBettiLabels = [b % mult for b in iBettis]

			#properly name the apery set elements
			name_map = {}
			for ii, b in enumerate(oBettis):
				val = b % mult
				if val not in name_map:
					name_map[val] = 0
				else:
					name_map[val] += 1
				label = f"${val}_{{{name_map[val]}}}$"
				label_map[b] = label
				value_map[label] = b
				oBettiLabels.append(label)

		for ii in NSG.AperySet(mult):
			label_map[ii] = ii % mult
			value_map[ii % mult] = ii

		covers=[]
		##find all the cover relations between the elements
		for ind, ii in enumerate(Ap):
			for jj in Ap[:ind]:
				if (ii-jj) in gens and (ii-jj) != mult:
					covers.append((label_map[jj],label_map[ii]))

		if verbose:
			print(covers)

		#orders the cover relations by the minimal elements that represents the relationship between elements, currently not implemented
		#coversOrdered=[]
		#for ii in Ap:
		#    for jj in covers:
		#        if ((jj[1]-jj[0])%mult)==(ii%mult):
		#            coversOrdered.append(jj)
		#print(coversOrdered)
		Ap=sorted(NSG.AperySet(mult).copy())

		#creates the poset based off the Apery Set modulo the multiplicty and the cover relations
		Comb=2*[0]
		Comb[0]=[x%mult for x in Ap] + oBettiLabels
		Comb[1]=covers
		#Comb[1]=coversOrdered
		PP=Poset(Comb,cover_relations=True)
		if plot: #returns as a poset object if plot set to False
			HH=PP.hasse_diagram() #turns the Poset object into a Hasse Diagram object

			#if colored, colors each edge by the element the edge represents
			if colored:
				colors=['red','mediumblue','forestgreen','darkmagenta','teal','orangered','olive','deeppink','gold','deepskyblue','indigo']
				count = -1
				for mm in gens[1:]:
					count += 1
					for nn in Comb[1]:
						if ((value_map[nn[1]]-value_map[nn[0]])%mult)==(mm%mult):
							HH.set_edge_label(nn[0],nn[1],count%11)
				colored={ii:colors[ii] for ii in [0..10]}
			dd=KunzPosetCoordinates(NSG,shift,verbose,vector_directions,show_bettis) #determines the coordinates for each vertex in the poset
			if verbose:
				print("DD:")
				print(dd)
				print()

	#creates an apery poset
	else:
		if show_bettis:
			bettis = NSG.BettiElements()
			iBettis = [b for ii, b in enumerate(bettis) if b in Ap]
			oBettis = [b for ii, b in enumerate(bettis) if b not in Ap]
			Ap += oBettis

			iBettiLabels = iBettis
			oBettiLabels = oBettis
		covers=[]
		#find all the cover relations between the elements
		for ind, ii in enumerate(Ap):
			for jj in Ap[:ind]:
				if (ii-jj) in gens and (ii - jj) != mult:
					covers.append((jj,ii))

		#orders the cover relations by the minimal elements that represents the relationship between elements, currently not implemented
		#coversOrdered=[]
		#for ii in Ap:
		#    for jj in covers:
		#        if ((jj[1]-jj[0])%mult)==(ii%mult):
		#            coversOrdered.append(jj)
		#print(coversOrdered)

		#creates the poset based off the Apery Set and the cover relations
		Comb=2*[0]
		Comb[0]=Ap
		Comb[1]=covers
		#Comb[1]=coversOrdered
		PP=Poset(Comb,cover_relations=True)
		if plot:
			HH=PP.hasse_diagram() #turns the Poset object into a Hasse Diagram object

			#if colored, colors each edge by the element the edge represents
			if colored:
				colors=['red','mediumblue','forestgreen','darkmagenta','teal','orangered','olive','deeppink','gold','deepskyblue','indigo']
				count = -1
				for mm in gens[1:]:
					count += 1
					for nn in Comb[1]:
						if ((nn[1]-nn[0]))==(mm):
							HH.set_edge_label(nn[0],nn[1],count%11)
				colored={ii:colors[ii] for ii in [0..10]}

			#determines the coordinates for each vertex in the poset
			dd=AperyPosetCoordinates(NSG,shift,verbose,vector_directions,show_bettis)

	if verbose:
		print('cover relations: '+str(covers))
		print('colored: ' +str(colored))
	if plot:
		vcolors = {}
		if colored:
			if partition_bettis:
				polys = []
				oBettiParts = []
				kPoset = KunzPoset(numerical_semigroup=NSG)
				for i in range(len(oBettis)):
					eqn = [0 for j in range(mult)]
					facts = NSG.Factorizations(oBettis[i])
					nonMultFacts = [f for f in facts if f[0] == 0]
					multFacts = [f for f in facts if f[0] != 0]
					multFact = max(multFacts, key=lambda x:x[0])
					assert (len(nonMultFacts) > 0) and (len(multFacts) > 0)
					for j in range(1, len(nonMultFacts[0])):
						idx = S.gens[j] % mult
						eqn[idx] = nonMultFacts[0][j] - multFact[j]
					eq = Polyhedron(eqns=[eqn])
					poly = kPoset.Face().intersection(eq)

					polyInd = -1
					for j, p in enumerate(polys):
						if p == poly:
							polyInd = j
							oBettiParts[j].append(oBettiLabels[i])
							break
						
					if polyInd == -1:
						polyInd = len(polys)
						polys.append(poly)
						oBettiParts.append([oBettiLabels[i]])

				vcolors = {'lightgray' : iBettiLabels}
				oBettiColors = ['lightcoral', 'navajowhite', 'springgreen', 'aquamarine', 'turquoise', 'skyblue', 'lavendar', 'plum']
				assert len(oBettiParts) <= len(oBettiColors)
				print(f"We have {len(oBettiParts)} different partitions of outer bettis")
				print(oBettiParts)
				for i, p in enumerate(polys):
					print(f"Poly {i} has dimension {p.dimension()}")

				for i in range(len(oBettiParts)):
					vcolors[oBettiColors[i]] = oBettiParts[i]
			else:
				vcolors={'lightgray' : iBettiLabels, 'lightcoral': oBettiLabels}
		return HH.plot(pos=dd,color_by_label=colored,figsize=fsize,vertex_size=vsize,vertex_colors=vcolors)  #plots the pose
	return PP #returns poset type object if plot set to False

def CheckVectorDirections(num_gens,vector_directions):
	if vector_directions is not None:
		# Check to ensure vector_directions is properly formatted
		if not type(vector_directions) is dict:
			return False
		for i in range(num_gens):
			if i not in vector_directions:
				return False
			if not type(vector_directions[i]) is tuple or len(vector_directions[i]) != 2:
				return False
	return True
