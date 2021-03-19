#include <stdio.h>
#include <ppl.hh>
#include <ppl_c.h>
#include <gmpxx.h>
#include <list>
#include <fstream>
#include "library/ppl_test.hh"
#include <math.h>
#include <stdlib.h>
#include <iostream>
#include <gmp.h>
#include <sstream>
#include "library/files.hh"

using namespace IO_Operators;
#define rate 1000 // multiply data with rate because PPL handles integers only

using namespace std;

class State {

public:
	int id = 0, numChild = 0, *childs, numZ = 0, *setZ, consistencyLevel = -1;

	Pointset_Powerset<C_Polyhedron> zeroConsistency;
	Pointset_Powerset<C_Polyhedron> nConsistency;
	Pointset_Powerset<C_Polyhedron> * consList;

public:
	void init1(int dimention, int numChild) {
		Pointset_Powerset<C_Polyhedron> zC(dimention, EMPTY);
		Pointset_Powerset<C_Polyhedron> nC(dimention, EMPTY);
		zeroConsistency = zC;
		nConsistency = nC;
		setZ = new int[numChild];
		childs = new int[numChild];

	}

public:
	void init2(int dimention, int numState) {

		consList = new Pointset_Powerset<C_Polyhedron> [numState];

		Pointset_Powerset<C_Polyhedron> nC(dimention, EMPTY);
		for (int i = 0; i < numState; i++)
			consList[i] = nC;

	}

};

class Edge {

public:
	int startState, endState;
public:
	float low = -1, up = -1;
public:
	string lowPara = "-1", upPara = "-1";
};

// this function to get the order of a variable based on the value of the string input

int choseVariable(string names[], int ne, string s) {
	int t = -1;

	for (int i = 0; i < ne; i++)
		if (names[i] == s) {
			t = i;
			break;
		}
	return t;

}

// this function is used to get the position of an element in the array

int getPosition(int a[], int e, int size) {

	int p = -1;
	for (int i = 0; i < size; i++)
		if (e == a[i]) {
			p = i;
			break;
		}

	return p;
}

void intTobinary(int n, int p[]) {
	int i = 0;
	while (n != 0) {
		p[i] = n % 2;
		i++;
		n = n / 2;
	}

}

Edge getEdge(Edge edges[], int ne, int start, int end) {
	Edge ed;
	for (int i = 0; i < ne; i++)
		if (edges[i].startState == start && edges[i].endState == end)
			ed = edges[i];
	return ed;

}

// this function is used to compute the union of 2 polyhedrons that are store in Pointset_Powerset

void unionComp(Pointset_Powerset<C_Polyhedron> &a,
		Pointset_Powerset<C_Polyhedron> b) {

	for (Pointset_Powerset<C_Polyhedron>::const_iterator it = b.begin(), b_end =
			b.end(); it != b_end; ++it) {
		a.add_disjunct(it->pointset());
	}

}

string varToString(int n) {
	string name, stra, strb, alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
	int a = n / 26;
	int b = n % 26;
	stringstream ss, ss1;
	ss << alphabet[b];
	ss1 << a;

	return (a > 0) ? (ss.str() + ss1.str()) : (ss.str());

}

string replaceString(string sa, string sb, string sc) {

	string sb1 = " " + sb + " ";
	string sb2 = " -" + sb + " ";
	int t = sa.find(sb1);
	while (t >= 0) {
		sa.replace(t, sb1.length(), " " + sc + " ");
		t = sa.find(sb1);

	}
	t = sa.find(sb2);
	while (t >= 0) {
		sa.replace(t, sb2.length(), " -" + sc + " ");
		t = sa.find(sb2);

	}

	return sa;

}

string convertString(string st1, int r) {
	st1 = replaceString(st1, ",", " |");
	string st2 = st1;
	istringstream iss(st1);
	float val = 0;
	do {
		string sub;
		iss >> sub;
		istringstream(sub) >> val;
		if (val != 0) {
			val = val / r;
			stringstream ss;
			ss << val;
			string sval = ss.str();
			st2 = replaceString(st2, sub, sval);
		}

	} while (iss);
	st2 = replaceString(st2, " |", ",");
	return st2;
}

C_Polyhedron localConsistency(State s, int cS[], int size, Edge * edges,
		int numState, string variNames[], int numVari, int numTran) {

	C_Polyhedron sumUp(numVari + 1), sumUp1(numVari + 1, EMPTY), sumLow(
			numVari + 1), lowUp(numVari + 1), CP(numVari + 1), pCheck(
			numVari + 1);
	Constraint_System cs1, cs2, cCheck;
	Linear_Expression eup, elow, euplow, ln;

	// only compute local consistency when the number of successor > 0
	if (size > 0) {
		for (int i = 0; i < size; i++) {

			Linear_Expression l;
			Constraint_System cs3;
			C_Polyhedron cp(numVari + 1);

			Edge ed = getEdge(edges, numTran, s.id, cS[i]);

			// if upPara is a parameter will  add it to a linear expression

			//	if (choseVariable(variNames, numVari,edges[s.id * numState + cS[i]].upPara) >= 0)

			if (choseVariable(variNames, numVari, ed.upPara) >= 0)

			{

				eup += Variable(choseVariable(variNames, numVari,
				//edges[s.id * numState + cS[i]].upPara)
						ed.upPara)

						);
				l = l + Variable(choseVariable(variNames, numVari,
				//edges[s.id * numState + cS[i]].upPara)
						ed.upPara)

						);

				// add 2 constraints to make sure that every parameter >=0 and <=1

				cCheck.insert(Variable(choseVariable(variNames, numVari,
						ed.upPara)) >= 0);
				cCheck.insert(Variable(choseVariable(variNames, numVari,
						ed.upPara)) <= rate);

			}

			// if upPara is a number we will  add it to other linear expression
			else {

				eup += ed.up;

				l = l + ed.up;

			}

			// the same solution with low parameter

			if (choseVariable(variNames, numVari,
					ed.lowPara) >= 0

			) {

				elow += Variable(choseVariable(variNames, numVari,
						ed.lowPara));
				l = l - Variable(choseVariable(variNames, numVari,
						ed.lowPara

						));
				cCheck.insert(Variable(choseVariable(variNames, numVari,
						ed.lowPara

						)) >= 0);
				cCheck.insert(Variable(choseVariable(variNames, numVari,
						ed.lowPara)) <= rate);

			} else {

				elow += ed.low;
				l = l - ed.low;

			}
			cs3.insert(l >= 0);
			cp.add_constraints(cs3);
			lowUp.intersection_assign(cp);
		}

		// sum of all up value greater is than 1 ( here 1 is replaced by rate)
		cs1.insert(eup >= rate);
		// sum of all low value is smaller than 1 ( here 1 is replaced by rate)
		cs2.insert(elow <= rate);
		sumUp.add_constraints(cs1);
		sumLow.add_constraints(cs2);
		sumUp.intersection_assign(sumLow);
		sumUp.intersection_assign(lowUp);
		pCheck.add_constraints(cCheck);
		sumUp.intersection_assign(pCheck);

	}

	else {
		sumUp = sumUp1;

	}

	return (sumUp);
}

void nConsistency(State *s, State states[], Edge * edges, int numState,
		string variNames[], int numVari, int numTran) {

	Pointset_Powerset<C_Polyhedron> pCheck(numVari + 1, EMPTY); // se xoa
	Pointset_Powerset<C_Polyhedron> nCons(numVari + 1, EMPTY);

	if (s->numChild > 0) {

		// Z0 has 2^number_element of subset X
		int p = pow(2, s->numZ);

		//computing Cons of every subset X of set Z
		// this will eliminate gradually element in successor of s then compute Cons of subset X

		for (int i = 1; i < p; i++) {

			C_Polyhedron low(numVari + 1), low1(numVari + 1), lowUp(
					numVari + 1), lc(numVari + 1);
			Pointset_Powerset<C_Polyhedron> intersection(numVari + 1, EMPTY);
			Pointset_Powerset<C_Polyhedron> intersection1(numVari + 1, EMPTY);

			int succMinusx[s->numChild];
			int nc = s->numChild;
			int B[s->numZ];

			for (int i1 = 0; i1 < s->numZ; i1++)
				B[i1] = 0;
			// store successor of s in another array
			for (int k = 0; k < s->numChild; k++)
				succMinusx[k] = s->childs[k];

			intTobinary(i, B); // call function

			for (int k = 0; k < s->numZ; k++)
				if (B[k] == 1) {

					// computing posittion
					int p = getPosition(succMinusx, s->setZ[k], nc);
					Constraint_System cs;
					Linear_Expression l;

					// sum all low value and assign this sum = 0 according to Algorithm
					Edge ed = getEdge(edges, numTran, s->id, succMinusx[p]);

					if (choseVariable(variNames, numVari,
							ed.lowPara) >= 0) {
						l += Variable(choseVariable(variNames, numVari,
								ed.lowPara));

						cs.insert(l == 0);
						low1.add_constraints(cs);
						low.intersection_assign(low1);
					}

					succMinusx[p] = succMinusx[nc - 1];
					nc--;
				}
			// compute local consitency according to Algorithm
			lc = localConsistency(*s, succMinusx, nc, edges, numState,
					variNames, numVari, numTran);
			lc.intersection_assign(low);
			intersection1.add_disjunct(lc);
			// computing intersection of all n-1 consistency of  successor - X

			intersection = states[succMinusx[0]].zeroConsistency;

			for (int i1 = 0; i1 < nc; i1++)
				intersection.intersection_assign(
						states[succMinusx[i1]].zeroConsistency);
			intersection.intersection_assign(intersection1);
			unionComp(nCons, intersection);
		}

		C_Polyhedron emty = localConsistency(*s, s->childs, s->numChild, edges,
				numState, variNames, numVari, numTran);
		Pointset_Powerset<C_Polyhedron> emtyP(numVari + 1, EMPTY);
		Pointset_Powerset<C_Polyhedron> inters(numVari + 1, EMPTY);
		inters = states[s->childs[0]].zeroConsistency;
		emtyP.add_disjunct(emty);

		// union of Cons.n.X of all subset X
		for (int i = 1; i < s->numChild; i++) {

			inters.intersection_assign(states[s->childs[i]].zeroConsistency);
		}

		inters.intersection_assign(emtyP);


		unionComp(nCons, inters);

	}
	s->nConsistency = nCons;


}

// this function is used to compute the zero consistency of s
// the way to compute zero consistency is similar to nConsistency function, but it is more simple

void zeroConsistency(State* s, Edge * edges, int numState, string variNames[],
		int numVari, int numTran) {
	int p = pow(2, s->numZ);

	for (int i = 1; i < p; i++) {

		C_Polyhedron low(numVari + 1), low1(numVari + 1), lowUp(numVari + 1),
				lc(numVari + 1);

		int succMinusx[s->numChild];
		int nc = s->numChild;
		int B[s->numZ];
		for (int i1 = 0; i1 < s->numZ; i1++)
			B[i1] = 0;
		for (int k = 0; k < s->numChild; k++)
			succMinusx[k] = s->childs[k];

		intTobinary(i, B); // call function

		for (int k = 0; k < s->numZ; k++)
			if (B[k] == 1) {

				int p = getPosition(succMinusx, s->setZ[k], nc);
				Constraint_System cs;
				Linear_Expression l;

				Edge ed = getEdge(edges, numTran, s->id, succMinusx[p]);

				if (choseVariable(variNames, numVari,
						ed.lowPara) >= 0

				) {

					l += Variable(choseVariable(variNames, numVari,
							ed.lowPara));
					cs.insert(l == 0);
					low1.add_constraints(cs);
					low.intersection_assign(low1);
				}



				succMinusx[p] = succMinusx[nc - 1];
				nc--;
			}


		lc = localConsistency(*s, succMinusx, nc, edges, numState, variNames,
				numVari, numTran);
		lc.intersection_assign(low);
		s->zeroConsistency.add_disjunct(lc);
	}
	C_Polyhedron emty = localConsistency(*s, s->childs, s->numChild, edges,
			numState, variNames, numVari, numTran);
	s->zeroConsistency.add_disjunct(emty);


}

void getData(char filename[20], string names[], State *states, Edge * edges,
		int numState, int numVari) {
	string l;
	ifstream mf(filename);

	// caculating number of child for each state - optimize memory
	int nbChild[numState];

	for (int j = 0; j < numState; j++)
		nbChild[j] = 0;

	for (int i = 0; i < numState + 4; i++)
		getline(mf, l);

	while (getline(mf, l)) {
		istringstream iss(l);
		int val;
		string sub;
		iss >> sub;
		istringstream(sub) >> val;
		for (int j = 0; j < numState; j++)
			if (val == j)
				nbChild[j]++;
		iss.clear();
	}

	for (int j = 0; j < numState; j++)
		states[j].init1(numVari + 1, nbChild[j]);
	for (int j = 0; j < numState; j++)
		states[j].init2(numVari + 1, numState);

	string line;
	ifstream myfile(filename);
	for (int i = 0; i < numState + 4; i++)
		getline(myfile, line);

	int numVari1 = 0;

// get value for every edges
	int index = 0;

	while (getline(myfile, line)) {

		istringstream iss(line);
		int row, column;
		string sub;
		iss >> sub;
		istringstream(sub) >> row;
		iss >> sub;
		iss >> sub;
		istringstream(sub) >> column;

		//moi them
		edges[index].startState = row;
		edges[index].endState = column;

		if (iss)
			iss >> sub;
		edges[index].lowPara = sub;

		float low = -1, low1 = -1, up = -1, up1 = -1;

		istringstream(sub) >> low;

		if (low > 0) { // value is number :2 3 4..
			edges[index].low = low * rate;

			states[row].numChild++;
			states[row].childs[states[row].numChild - 1] = column;

		} else {
			istringstream("1" + sub) >> low1;
			if (low1 - low == 1) {
				if (choseVariable(names, numVari1, sub) < 0) {
					names[numVari1] = sub;
					numVari1++;

				}
				states[row].numChild++;
				states[row].childs[states[row].numChild - 1] = column;

				edges[index].low = -1;

				states[row].numZ++;
				states[row].setZ[states[row].numZ - 1] = column;

			} else {
				states[row].numChild++;
				states[row].childs[states[row].numChild - 1] = column;
				edges[index].low = 0;

				states[row].numZ++;
				states[row].setZ[states[row].numZ - 1] = column;

			}

		}

		if (iss)
			iss >> sub;
		edges[index].upPara = sub;

		istringstream(sub) >> up;

		if (up > 0) {
			edges[index].up = up * rate;

		}

		else {

			istringstream("1" + sub) >> up1;

			if (up1 - up == 1) {

				if (choseVariable(names, numVari1, sub) < 0) {
					names[numVari1] = sub;
					numVari1++;
					edges[index].up = -1;

				}

			} else {
				edges[index].up = 0;

			}
		}
		index++;

	}

	myfile.close();
}

void init(char filename[20], int *numState, int *numVari, int *numTran) {
	int num = 0;
	string line;
	ifstream myfile(filename);

	if (!myfile) {
		printf("Error orcured when open file\n");
		exit(0);
	}

	getline(myfile, line);
	istringstream iss(line);
	string sub;
	iss >> sub;
	iss >> sub;
	istringstream(sub) >> *numState;
	iss.clear();

	getline(myfile, line);
	istringstream iss1(line);
	iss1 >> sub;
	iss1 >> sub;
	istringstream(sub) >> *numVari;

	while (getline(myfile, line)) {
		num++;
	}
	*numTran = (num - *numState - 2);

}

void nConsistency1(State *s, int n, State states[], Edge * edges, int numState,
		string variNames[], int numVari, int numTran) {

	Pointset_Powerset<C_Polyhedron> chk(numVari + 1, EMPTY);
	// check if n-1 consistency = false -> n consistency = false (do not need compute it anymore)
	bool chkFalse = (s->consList[n - 1] == chk);
	int count = 0;
	float sum = 0;

	for (int i = 0; i < s->numChild; i++)
		if (choseVariable(variNames, numVari,
				getEdge(edges, numTran, s->id, s->childs[i]).upPara) < 0) {
			count++;
			sum = sum + getEdge(edges, numTran, s->id, s->childs[i]).up;
		}
	if ((count == s->numChild) && sum < rate)
		chkFalse = true;

	if (chkFalse) {
		s->consistencyLevel++;
	} else if (s->consistencyLevel == n - 1) {

		Pointset_Powerset<C_Polyhedron> pCheck(numVari + 1); // true value
		Pointset_Powerset<C_Polyhedron> pCheck1(numVari + 1, EMPTY); // false value
		bool chk = false;
		int arrX[numState], ne = 0; // to store states which have value = false are in Z

		int minusX[s->numChild], nem = s->numChild;
		int Z1[s->numChild], nez = 0;

		for (int i = 0; i < s->numChild; i++) {
			minusX[i] = s->childs[i];
		}
		for (int i = 0; i < s->numChild; i++) {
			Z1[i] = s->setZ[i];
		}

		nez = s->numZ;

		for (int i = 0; i < s->numChild; i++)
			if (states[s->childs[i]].consList[n - 1] == pCheck1) {

				int p = getPosition(s->setZ, s->childs[i], s->numZ);
				if (p < 0) {

					s->consistencyLevel = s->consistencyLevel + 1;
					chk = true;
					break;
				} else {
					minusX[i] = minusX[nem - 1];
					nem--;
					Z1[p] = Z1[nez - 1];
					nez--;
					arrX[ne] = s->childs[i]; // store state which has value = false is in child
					ne++;
				}
			}

		if (chk == false) {
			Pointset_Powerset<C_Polyhedron> nCons(numVari + 1, EMPTY);

			if (ne > 0) {

				C_Polyhedron lowo(numVari + 1), lowo1(numVari + 1), lco(
						numVari + 1);
				Pointset_Powerset<C_Polyhedron> intero(numVari + 1, EMPTY);

				for (int k = 0; k < ne; k++) {
					Constraint_System cs;
					Linear_Expression l;

					Edge ed = getEdge(edges, numTran, s->id, arrX[k]);

					if (choseVariable(variNames, numVari,
							ed.lowPara) >= 0) {
						l += Variable(choseVariable(variNames, numVari,
								ed.lowPara));
						cs.insert(l == 0);
						lowo1.add_constraints(cs);
						lowo.intersection_assign(lowo1);
					}
				}

				int po = pow(2, nez);
				for (int i = 1; i < po; i++) {
					C_Polyhedron low(numVari + 1), low1(numVari + 1), lowUp(
							numVari + 1), lc(numVari + 1);
					Pointset_Powerset<C_Polyhedron> intersection(numVari + 1,
							EMPTY);
					Pointset_Powerset<C_Polyhedron> intersection1(numVari + 1,
							EMPTY);
					int succMinusx[s->numChild];
					int nc = nem;

					int B[s->numZ];
					for (int i1 = 0; i1 < s->numZ; i1++)
						B[i1] = 0;

					for (int k = 0; k < nem; k++)
						succMinusx[k] = minusX[k];
					intTobinary(i, B); // call function

					for (int k = 0; k < nez; k++)
						if (B[k] == 1) {

							int p = getPosition(succMinusx, Z1[k], nc);
							Constraint_System cs;
							Linear_Expression l;
							Edge ed = getEdge(edges, numTran, s->id,
									succMinusx[p]);

							if (choseVariable(variNames, numVari,
									ed.lowPara) >= 0) {
								l += Variable(choseVariable(variNames, numVari,
										ed.lowPara));
								cs.insert(l == 0);
								low1.add_constraints(cs);
								low.intersection_assign(low1);
							}
							succMinusx[p] = succMinusx[nc - 1];
							nc--;
						}

					lc = localConsistency(*s, succMinusx, nc, edges, numState,
							variNames, numVari, numTran);
					low.intersection_assign(lowo);
					lc.intersection_assign(low);
					intersection1.add_disjunct(lc);
					intersection = states[succMinusx[0]].consList[n - 1];
					for (int i1 = 0; i1 < nc; i1++)
						intersection.intersection_assign(
								states[succMinusx[i1]].consList[n - 1]);
					intersection.intersection_assign(intersection1);
					unionComp(nCons, intersection);
					// if Cons(x)= true, break from  this loop
					if (nCons == pCheck)
						break;
				}

				C_Polyhedron emty = localConsistency(*s, minusX, nem, edges,
						numState, variNames, numVari, numTran);
				emty.intersection_assign(lowo);
				Pointset_Powerset<C_Polyhedron> emtyP(numVari + 1, EMPTY);
				Pointset_Powerset<C_Polyhedron> inters(numVari + 1, EMPTY);
				inters = states[minusX[0]].consList[n - 1];
				emtyP.add_disjunct(emty);

				for (int i = 1; i < nem; i++) {
					inters.intersection_assign(
							states[minusX[i]].consList[n - 1]);
				}

				inters.intersection_assign(emtyP);
				unionComp(nCons, inters);
				s->consList[n] = nCons;
				s->consistencyLevel = s->consistencyLevel + 1;

			}

			else {

				int p = pow(2, s->numZ);
				//Variable(numVariable);
				//computing cons 0-x of every subset of set Z
				for (int i = 1; i < p; i++) {
					C_Polyhedron low(numVari + 1), low1(numVari + 1), lowUp(
							numVari + 1), lc(numVari + 1);
					Pointset_Powerset<C_Polyhedron> intersection(numVari + 1,
							EMPTY);
					Pointset_Powerset<C_Polyhedron> intersection1(numVari + 1,
							EMPTY);

					int succMinusx[s->numChild];
					int nc = s->numChild;
					int B[s->numZ];
					for (int i1 = 0; i1 < s->numZ; i1++)
						B[i1] = 0;

					for (int k = 0; k < s->numChild; k++)
						succMinusx[k] = s->childs[k];

					intTobinary(i, B); // call function
					for (int k = 0; k < s->numZ; k++)
						if (B[k] == 1) {
							int p = getPosition(succMinusx, s->setZ[k], nc);
							Constraint_System cs;
							Linear_Expression l;

							Edge ed = getEdge(edges, numTran, s->id,
									succMinusx[p]);

							if (choseVariable(variNames, numVari,
									ed.lowPara) >= 0) {
								l += Variable(choseVariable(variNames, numVari,
										ed.lowPara

										));
								cs.insert(l == 0);
								low1.add_constraints(cs);
								low.intersection_assign(low1);
							}

							succMinusx[p] = succMinusx[nc - 1];
							nc--;
						}
					lc = localConsistency(*s, succMinusx, nc, edges, numState,
							variNames, numVari, numTran);
					lc.intersection_assign(low);
					intersection1.add_disjunct(lc);
					intersection = states[succMinusx[0]].consList[n - 1];
					for (int i1 = 0; i1 < nc; i1++)
						intersection.intersection_assign(
								states[succMinusx[i1]].consList[n - 1]);
					intersection.intersection_assign(intersection1);
					unionComp(nCons, intersection);
					// if Cons(x)= true, break from  this loop
					if (nCons == pCheck)
						break;

				}

				C_Polyhedron emty = localConsistency(*s, s->childs, s->numChild,
						edges, numState, variNames, numVari, numTran);
				Pointset_Powerset<C_Polyhedron> emtyP(numVari + 1, EMPTY);
				Pointset_Powerset<C_Polyhedron> inters(numVari + 1, EMPTY);
				inters = states[s->childs[0]].consList[n - 1];
				emtyP.add_disjunct(emty);
				for (int i = 1; i < s->numChild; i++) {
					inters.intersection_assign(
							states[s->childs[i]].consList[n - 1]);
				}

				inters.intersection_assign(emtyP);
				unionComp(nCons, inters);
				s->consList[n] = nCons;
				s->consistencyLevel = s->consistencyLevel + 1;
			}
		}
	}

}

void zeroConsistency1(State* s, Edge * edges, int numState, string variNames[],
		int numVari, int numTran) {

	bool chk = true;
	int count = 0;
	float sum = 0;

	for (int i = 0; i < s->numChild; i++)
		if (choseVariable(variNames, numVari,
				getEdge(edges, numTran, s->id, s->childs[i]).upPara) < 0) {
			count++;
			sum = sum + getEdge(edges, numTran, s->id, s->childs[i]).up;

		}
	if ((count == s->numChild) && sum < rate)
		chk = false;

	if (!chk)
		s->consistencyLevel++;
	else

	if (s->consistencyLevel < 0) {

		Pointset_Powerset<C_Polyhedron> pCheck(numVari + 1);
		int p = pow(2, s->numZ);

		//computing cons 0-x of every subset of set Z
		for (int i = 1; i < p; i++) {
			C_Polyhedron low(numVari + 1), low1(numVari + 1), lowUp(
					numVari + 1), lc(numVari + 1);
			int succMinusx[s->numChild];

			int nc = s->numChild;

			int B[s->numZ];
			for (int i1 = 0; i1 < s->numZ; i1++)
				B[i1] = 0;

			for (int k = 0; k < s->numChild; k++)
				succMinusx[k] = s->childs[k];
			intTobinary(i, B); // call function

			for (int k = 0; k < s->numZ; k++)
				if (B[k] == 1) {
					int p = getPosition(succMinusx, s->setZ[k], nc);
					Constraint_System cs;
					Linear_Expression l;

					Edge ed = getEdge(edges, numTran, s->id, succMinusx[p]);

					if (choseVariable(variNames, numVari,
					//edges[s->id * numState + succMinusx[p]].lowPara
							ed.lowPara) >= 0) {
						l += Variable(choseVariable(variNames, numVari,
						//edges[s->id * numState + succMinusx[p]].lowPara
								ed.lowPara));
						cs.insert(l == 0);
						low1.add_constraints(cs);
						low.intersection_assign(low1);
					}
					succMinusx[p] = succMinusx[nc - 1];
					nc--;
				}
			lc = localConsistency(*s, succMinusx, nc, edges, numState,
					variNames, numVari, numTran);
			lc.intersection_assign(low);
			s->consList[0].add_disjunct(lc);
			// consList[0]= true we can break from thi loop
			if (s->consList[0] == pCheck)
				break;
		}
		C_Polyhedron emty = localConsistency(*s, s->childs, s->numChild, edges,
				numState, variNames, numVari, numTran);
		s->consList[0].add_disjunct(emty);
		s->consistencyLevel = 0;
	}
}

void consistency(State * s, int n, State states[], Edge *edges, int numState,
		string variNames[], int numVari, int numTran) {

	if (n == 0)
		zeroConsistency1(s, edges, numState, variNames, numVari, numTran);

	else {

		int count = 0;
		for (int j = 0; j < s->numChild; j++)
			if ((states + s->childs[j])->consistencyLevel >= (n - 1))
				count++;

		if (count == s->numChild)

			nConsistency1(s, n, states, edges, numState, variNames, numVari,
					numTran);
		else

		{
			for (int i = 0; i < s->numChild; i++)
				consistency((states + s->childs[i]), n - 1, states, edges,
						numState, variNames, numVari, numTran);
			nConsistency1(s, n, states, edges, numState, variNames, numVari,
					numTran);

		}

	}
}

string primAlgorithm(State states[], Edge *edges, string variNames[],
		int numState, int numVari, int numTran) {

	string result;
	Pointset_Powerset<C_Polyhedron> pCheck(numVari + 1, EMPTY);

	int k = 0;
	bool ok;

	for (int i = 0; i < numState; i++)

	{
		zeroConsistency(states + i, edges, numState, variNames, numVari,
				numTran);
		(states + i)->nConsistency = (states + i)->zeroConsistency;


	}

	// while  n consistency of initial state != false will compute n consistency continuously

	if (states[0].nConsistency != pCheck)

		while ((k < numState ) && (!ok)) {

			for (int i = 0; i < numState; i++) {

				nConsistency(states + i, states, edges, numState, variNames,
						numVari, numTran);

				ok = (states[0].nConsistency == pCheck);

			}
			// check n consistency of initial state = fale ?

			ok = (states[0].nConsistency == pCheck);

			if (!ok)
				for (int i = 0; i < numState; i++) {

					states[i].zeroConsistency = states[i].nConsistency;

				}
			k++;
			cout << "finish with n =" << k << "\n";
		}

	stringstream ss;
	ss << states[0].zeroConsistency;
	result = ss.str();

	k--;
	if (k < 0)
		std::cout << "n = 0" << endl;
	else
		std::cout << "n = " << k << endl;

	return result;
}

string optimAlgorithm(State states[], Edge *edges, string variNames[],
		int numState, int numVari, int numTran) {

	string result;
	int k = 0, p = -1;
	bool ok;
	Pointset_Powerset<C_Polyhedron> pCheck(1, EMPTY);
	Pointset_Powerset<C_Polyhedron> pCheck1(1);

	while ((k < numState) && (!ok)) {
		consistency(states + 0, k, states, edges, numState, variNames, numVari,
				numTran);
		cout << "finish with n =" << k << "\n";

		ok = (states->consList[k] == pCheck);
		if (ok)
			p = k - 1;
		else
			p = k;
		k++;

	}

	Pointset_Powerset<C_Polyhedron> pResult(numVari + 1, EMPTY);

	if (states->consistencyLevel - 1 < 0) {
		pResult = (states)->consList[0];
		cout << "n=" << 0 << endl;
	} else

	{
		pResult = (states)->consList[states->consistencyLevel - 1];
		cout << "n= " << p << endl;
	}
	stringstream ss;
	ss << pResult;
	result = ss.str();

	return result;
}



int main(int argc, char ** args) {


	if (argc < 3)
		cout << "not enough parameters\n";
	else {
		string result;
		clock_t start, finish;
		start = clock();

		char * fileName;
		fileName = args[1];

		istringstream iss(args[2]);
		string opt;
		iss >> opt;
		int numState, numVari, numTran;

		init(fileName, &numState, &numVari, &numTran);
		string variNames[numVari + 1];
		Edge * edges = new Edge[numTran];
		State * states = new State[numState];

		for (int i = 0; i < numState; i++)
			states[i].id = i;
		getData(fileName, variNames, states, edges, numState, numVari);

			if (opt == "1") {

			result = primAlgorithm(states, edges, variNames, numState, numVari,
					numTran);
			for (int i = 0; i < numVari; i++) {
				result = replaceString(result, varToString(i), variNames[i]);
			}
			finish = clock();

		} else if (opt == "2")

		{
			result = optimAlgorithm(states, edges, variNames, numState, numVari,
					numTran);
			for (int i = 0; i < numVari; i++) {
				result = replaceString(result, varToString(i), variNames[i]);
			}
			finish = clock();
		}

		//cout << convertString(result,rate)<< endl;
		cout << result << endl;

		double duration = (double) (finish - start) / CLOCKS_PER_SEC;
		cout << "timing:   " << duration << endl;

		ofstream myfile1, myfile2, myfile3;

		myfile1.open("result.txt");


		stringstream ss1;
		ss1 << duration;
		string str1 = ss1.str();
		str1 = "=  " + str1 + "\n";
		myfile1 << fileName;
		myfile1 << str1;
		myfile1.close();




}
	return 0;

}

