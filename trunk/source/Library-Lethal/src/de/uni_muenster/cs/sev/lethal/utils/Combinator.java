/*
 * Copyright 2009 Dorothea Jansen <d.jansen@uni-muenster.de>, Martin Mohr <mohrfrosch@uni-muenster.de>, Irene Thesing <i_thes01@uni-muenster.de>, Anton Reis <antonreis@gmx.de>, Maria Schatz <m_scha17@uni-muenster.de>, Philipp Claves <philipp.claves@uni-muenster.de>, Sezar Jarrous <sezar.jarrous@gmail.com>
 *
 * This file is part of LETHAL.
 *
 * LETHAL is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * LETHAL is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with LETHAL.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_muenster.cs.sev.lethal.utils;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uni_muenster.cs.sev.lethal.treeautomata.common.FTAOps;

/**
 * Encapsulates several combinatorial algorithm. <br>
 * <br>
 * The algorithms: 
 * <ul>
 * <li> {@link #combine combine}: Given a set of instances of type S, calculates the n-fold Cartesian product.</li>
 * <li> {@link #cartesianProduct cartesianProduct}: Returns the Cartesian product of a given list of sets. </li>
 * <li> {@link #allListsContainingXCombine allListsContainingXCombine}: Given some set, an object and an integer n, the method 
 * creates all lists of given length consisting of elements
 * of the given set such that each list contains the given object. </li>
 * </ul>
 * 
 * @author Martin
 */

//TODO (Martin): Kommentare überprüfen!
public class Combinator {

	/**
	 * Given a set of instances of type S, calculates the n-fold Cartesian
	 * product, represented as the set of all lists of cardinal number n.
	 * 
	 * @param <S> type of objects occurring in the set
	 * @param myset given set of objects
	 * @param n	 dimension of the Cartesian product
	 * @return n-fold Cartesian product of the given set (myset^n)
	 */
	public static <S> Set<List<S>> combine(Set<S> myset, int n) {
		HashSet<List<S>> ret = new HashSet<List<S>>();
		/*
		 * myset^0 is the set of all lists of elements of myset, which contain
		 * exactly zero elements, i.e. the set which contains exactly the empty
		 * list.
		 */
		if (n == 0) {
			ret.add(new LinkedList<S>());
			return ret;
		} else
			/*
			 * myset^1 is the set of all lists of elements of myset, which contain
			 * exactly one element.
			 */
			if (n == 1) {
				for (S x : myset) {
					LinkedList<S> l = new LinkedList<S>();
					l.add(x);
					ret.add(l);
				}
				return ret;
			} else {
				Set<List<S>> rest = combine(myset,n-1);
				for (S x : myset) {
					/*
					 * Let l be a list of the returned set, then there exists an element x of myset
					 * that is the first element of l. Conversely, each element x of myset
					 * is the first element of some list l of the returned set.
					 * In particular, all lists of myset^n with first element x are constructed 
					 * by adding x to all lists of myset^{n-1}.
					 */
					for (List<S> l: rest) {
						l.add(0,x);
						ret.add(new LinkedList<S>(l));
						l.remove(0);
					}
				}
				return ret;
			}
	}


	/**
	 * Returns the Cartesian product of a given list of sets. <br>
	 * The idea is similar to the idea of combine, which is in fact 
	 * just a special case of a Cartesian product.
	 * 
	 * @param <S> type of the elements in the given sets
	 * @param sets list of sets to be set theoretically multiplied
	 * @return the Cartesian product of the given sets
	 */
	public static <S> Set<List<S>> cartesianProduct(List<Set<S>> sets) {
		HashSet<List<S>> ret = new HashSet<List<S>>();
		/*
		 * If the list of given sets is empty, the Cartesian product
		 * contains just the empty list.
		 */ 
		if (sets.size()==0) {
			ret.add(new LinkedList<S>());
			return ret;
		}
		/*
		 * If there is just one list set given, the Cartesian product
		 * consists all singleton lists, where the elements of the singleton 
		 * lists are the elements of the given set. 
		 */
		else {
			if (sets.size()==1) {
				// the (only) set to consider
				Set<S> A = sets.get(0);
				// for each element of A construct a singleton list
				for (S x: A) {
					LinkedList<S> l = new LinkedList<S>();
					l.add(x);
					ret.add(l);
				}
				return ret;
			}
			/*
			 * idea: CartesianProduct(A1,...,An) = 
			 * CartesianProduct(A1,CartesianProduct(A2,...,An))
			 */
			else {
				// A1
				Set<S> A1 = sets.get(0);
				// A := CartesianProduct(A2,...,An)
				Set<List<S>> A2toN = cartesianProduct(sets.subList(1, sets.size()));
				/* 
				 * CartesianProduct(A1,A): for each element x of A1 and each list l of A
				 * create a new list consisting of x and the elements of l.
				 */
				for (S x: A1) {
					for (List<S> l: A2toN) {
						l.add(0,x);
						ret.add(new LinkedList<S>(l));
						l.remove(0);
					}
				}
				return ret;
			}
		}
	}


	/**
	 * Computes the smallest set A of lists with the following properties:
	 * (i) for each l \in A: x \in A
	 * (ii) A contains all combinations of n elements of the union of the given set and {x} with property (i). <br>
	 * Idea: This set consists exactly of all lists (a_1,...,a_{j-1},x,a_{j+1},...,a_n) where
	 * the a_i are elements of the union of the given set and {x}. <br>
	 * Just used in {@link FTAOps#determinize}
	 * 
	 * @param <Q> type of elements
	 * @param set arbitrary set
	 * @param x arbitrary element 
	 * @param n STRICTLY POSITIVE number which describes the length of the lists to return
	 * @return the smallest set A of lists with the following properties: 
	 * (i) for each l \in A: x \in A, 
	 * (ii) A contains all combinations of n elements of (set \cup {x})
	 */
	public static <Q> Set<List<Q>> allListsContainingXCombine(Set<Q> set, Q x, int n) {
		// union of set and {x}
		Set<Q> cpySet = new HashSet<Q>(set);
		Set<List<Q>> ret = new HashSet<List<Q>>();
		cpySet.add(x);
		/* 
		 * all lists with length n of elements of cpySet; 
		 * this shall become the (a_1,..,a_{j-1},a_{j+1},..,a_n)
		 */
		Set<List<Q>> foo = combine(cpySet,n-1);
		// create the (a_1,...,a_{j-1},x,a_{j+1},...,a_n)
		for (List<Q> l: foo) {
			for (int pos=0; pos<n; pos++) {
				l.add(pos, x);
				ret.add(new ArrayList<Q>(l));
				l.remove(pos);
			}	
		}
		return ret;
	}

}
