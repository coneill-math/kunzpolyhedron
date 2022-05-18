import numbers
import numpy as np

from sage.plot.plot3d.shapes import Sphere, Text, arrow3d

class Poset3D:

    def __init__(self, poset, coords, colors, arrowColors=None, vertexSize=1):
        els = poset.list()
        covers = poset.cover_relations()

        self.els = {}
        for e in els:
            self.els[e] = PosetElement3D(e, coords[e], colors[e], vertexSize)

        for c in covers:
            color = 'black'
            self.els[c[0]].addConnection(self.els[c[1]])
        
    def plot(self):
        keys = list(self.els.keys())
        g = self.els[keys[0]].plot()
        for i in range(1, len(keys)):
            g += self.els[keys[i]].plot()
        return g

class PosetElement3D:

    def __init__(self, label, coords, color='blue', vertexSize=1, opacity=0.5):
        # Validate inputs
        assert len(coords) == 3
        assert sum([isinstance(i, numbers.Number) for i in coords]) == 3
        assert isinstance(color, str)

        # Store inputs
        self.x = coords[0]
        self.y = coords[1]
        self.z = coords[2]
        self.label = label
        self.color = color
        self.vertexSize = vertexSize
        self.opacity = opacity
        self.arrows = []

    def addConnection(self, posetEl, color='black'):
        startPt = np.array([self.x, self.y, self.z])
        endPt = np.array([posetEl.x, posetEl.y, posetEl.z])

        diff = endPt - startPt
        diff = diff / np.linalg.norm(diff)

        startPt = startPt + diff * self.vertexSize
        endPt = endPt - diff * posetEl.vertexSize

        self.arrows.append(PosetArrow3D(startPt, endPt, color))

    def plot(self):
        s = Sphere(self.vertexSize, color=self.color, 
                opacity=self.opacity).translate(self.x, self.y, self.z)
        t = Text(self.label).translate(self.x, self.y, self.z)

        g = s + t
        for a in self.arrows:
            g += a.plot()
        return g

class PosetArrow3D:
    
    def __init__(self, startPt, endPt, color):
        self.startPt = startPt
        self.endPt = endPt
        self.color = color

    def plot(self):
        return arrow3d(self.startPt, self.endPt, color=self.color)

# How to generate a plot for a specific numerical semigroup
def exampleUsage():
    scale = 3
    S = NumericalSemigroup([55, 108, 126, 193])
    kPoset = KunzPoset(numerical_semigroup=S)
    coords = {x % S.gens[0] : S.Factorizations(x)[0][1:] for x in S.AperySet(S.gens[0])}
    for x in coords:
        for i in range(len(coords[x])):
            coords[x][i] *= scale
    colors = {i : 'blue' for i in coords.keys()}

    P = Poset3D(kPoset.poset, coords, colors)
    show(P.plot(), frame=False)
