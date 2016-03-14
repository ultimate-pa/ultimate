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
/**
 * 
 */
package de.uni_muenster.cs.sev.lethal.tree.common;


import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import de.uni_muenster.cs.sev.lethal.symbol.common.BiSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.common.Variable;
import de.uni_muenster.cs.sev.lethal.symbol.common.RankedSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.InnerSymbol;
import de.uni_muenster.cs.sev.lethal.symbol.standard.LeafSymbol;

/**
 * This class encapsulates some operations on variable trees, 
 * for example in order to find some variables in a variable tree or 
 * or to get the highest number of variables, which is relevant for applying homomorphisms.  
 * 
 * @see de.uni_muenster.cs.sev.lethal.hom.EasyHom
 * 
 * @author Dorothea, Irene, Martin
 */
public class VarTreeOps {


	/**
	 * Computes the highest variable number occurring in a given variable tree.
	 * 
	 * @param <F> type of function symbols occurring in the specified tree
	 * @param <V> type of variables occurring in the specified tree
	 * @param varTree tree to compute the highest variable number of
	 * @return highest variable number contained in the specified tree
	 */
	public static <F extends RankedSymbol, V extends Variable> int getHighestVariableNumber(Tree<? extends BiSymbol<F,V>> varTree) {
		return getHighestNumber(varTree, -1);
	}

	/**
	 * Helper method for getHighestVariableTree() - computes the highest variable number relative
	 * to a given maximum.
	 * 
	 * @param <F> type of function symbols occurring in the specified tree
	 * @param <V> type of variables occurring in the specified tree
	 * @param varTree tree to compute the highest variable number of
	 * @param max the already calculated temporary maximum
	 * @return the highest VariableNumber which is contained in this tree and is higher than max.
	 */
	private static <F extends RankedSymbol, V extends Variable> int getHighestNumber(Tree<? extends BiSymbol<F,V>> varTree, int max) {
		if (varTree.getSymbol().isLeafType()) {
			V var = varTree.getSymbol().asLeafSymbol();
			int nr = var.getComponentNumber();
			if (nr > max)
				return nr;
		}
		else {
			F root = varTree.getSymbol().asInnerSymbol();
			if (root.getArity() != 0){
				for (Tree<? extends BiSymbol<F,V>> sub: varTree.getSubTrees()){
					int nr = VarTreeOps.<F,V>getHighestNumber(sub, max);
					if (nr > max){
						max = nr;
					}		
				}
				return max;
			}
		}
		return max;
	}

	/**
	 * Checks whether a variable with the given number is contained in the given tree.
	 * 
	 * @param <F> type of function symbols occurring in the specified tree
	 * @param <V> type of variables occurring in the specified tree
	 * @param i the component number of the searched variable
	 * @param varTree variable tree to be examined
	 * @return true if a variable with the number i is contained in the given tree
	 */
	public static <F extends RankedSymbol, V extends Variable> boolean containsVariable(Tree<? extends BiSymbol<F,V>> varTree, int i) {
		if (varTree.getSymbol().isLeafType()) {
			V v = varTree.getSymbol().asLeafSymbol();
			return i == v.getComponentNumber();
		} else {
			for (Tree<? extends BiSymbol<F,V>> sub: varTree.getSubTrees()){
				if (VarTreeOps.<F,V>containsVariable(sub, i)){
					return true;
				}
			}
			return false;	    
		}
	}


	/**
	 * Checks whether a variable with the given number is contained in the given tree.
	 * 
	 * @param <F> type of function symbols occurring in the specified tree
	 * @param <V> type of variables occurring in the specified tree
	 * @param x the searched variable
	 * @param varTree variable tree to be examined
	 * @return true if a variable with the number i is contained in the given tree
	 */
	public static <F extends RankedSymbol, V extends Variable> boolean containsVariable(Tree<? extends BiSymbol<F,V>> varTree, V x) {
		if (varTree.getSymbol().isLeafType()) {
			return x.equals(varTree.getSymbol().asLeafSymbol());
		} else {
			for (Tree<? extends BiSymbol<F,V>> sub: varTree.getSubTrees()){
				if (VarTreeOps.<F,V>containsVariable(sub, x)){
					return true;
				}
			}
			return false;	    
		}
	} 

	/**
	 * Collects the variables occurring in the given tree.
	 * 
	 * @param <F> type of function symbols occurring in the specified tree
	 * @param <V> type of variables occurring in the specified tree
	 * @param varTree tree to collect the variables from
	 * @return all variables contained in the given tree 
	 */
	public static <F extends RankedSymbol, V extends Variable> Set<V> getVariables(Tree<BiSymbol<F,V>> varTree) {
		Set<V> vars = new HashSet<V>();
		if (varTree.getSymbol().isLeafType()) {
			V v = varTree.getSymbol().asLeafSymbol();
			vars.add(v);
		} else {
			for (Tree<BiSymbol<F,V>> sub: varTree.getSubTrees()){
				vars.addAll(VarTreeOps.<F,V>getVariables(sub));
			}  
		}
		return vars;
	}


	/**
	 * Computes the set of all function symbols occurring in the given tree.
	 * 
	 * @param <F> type of function symbols occurring in the specified tree
	 * @param <V> type of variables occurring in the specified tree
	 * @param varTree tree to collect the function symbols from
	 * @return set of all function symbols occurring in the given tree
	 */
	public static <F extends RankedSymbol, V extends Variable> Set<F> computeRankedSymbols(Tree<? extends BiSymbol<F,V>> varTree) {
		Stack<Tree<? extends BiSymbol<F,V>>> toDo = new Stack<Tree<? extends BiSymbol<F,V>>>();
		Set<F> ret = new HashSet<F>();
		toDo.push(varTree);
		while (!toDo.isEmpty()) {
			Tree<? extends BiSymbol<F,V>> s = toDo.pop();
			if (s.getSymbol().isInnerType())
				ret.add(s.getSymbol().asInnerSymbol());
			for (Tree<? extends BiSymbol<F,V>> s0: s.getSubTrees())
				toDo.push(s0);
		}
		return ret;
	}

	/**
	 * Replaces variables in a tree by a given list of trees - the indices of the
	 * list members correspond to the numbers of the variables to be replaced, i.e.
	 * if a variable with number i occurs in the variable tree, it is replaced by
	 * the i-th list member.
	 * 
	 * @param <F> type of function symbols occurring in specified tree
	 * @param <V> type of variables occurring in specified tree
	 * @param <U> type of tree to be returned
	 * @param varTree tree to be substituted
	 * @param replaceTrees the list of trees which shall replace the variables
	 * (i-th list member replaces variable with number i)
	 * @param tc a tree creator to produce the substituted tree
	 * @return a tree on which the variables are replaced by the trees specified in the given list
	 */
	public static <F extends RankedSymbol, 
	V extends Variable, 
	U extends Tree<F>> 
	U replaceVariables(Tree<? extends BiSymbol<F,V>> varTree, List<U> replaceTrees, TreeCreator<F,U> tc) {
		// if the symbol is an Variable, replace it by the according subtree
		if (varTree.getSymbol().isLeafType()) {
			int nr = varTree.getSymbol().asLeafSymbol().getComponentNumber();
			if (replaceTrees.size() <= nr){
				throw new IllegalArgumentException("The given List of replacing trees is not long enough, it must be bigger than " + nr );
			} else
				return replaceTrees.get(nr);
		} 
		// else it is a function symbol
		// look in all subtrees for variables and replace them recursively
		else {
			F sf = varTree.getSymbol().asInnerSymbol();
			List<? extends Tree<? extends BiSymbol<F,V>>> subs = varTree.getSubTrees();
			List<U> newsubs = new LinkedList<U>();
			// apply the function on the subtrees as long as all variables are reached an eliminated
			for (Tree<? extends BiSymbol<F,V>> sub: subs){
				newsubs.add(VarTreeOps.<F,V,U>replaceVariables(sub, replaceTrees, tc));
			}
			// produce the tree
			return tc.makeTree(sf, newsubs);
		}
	}


	/**
	 * Replaces variables in a tree by a given list of trees - the indices of the
	 * list members correspond to the numbers of the variables to be replaced, i.e.
	 * if a variable with number i occurs in the variable tree, it is replaced by
	 * the i-th list member.
	 * 
	 * @param <F> type of function symbols occurring in the specified tree
	 * @param <V> type of variables occurring in the specified tree
	 * @param <U> type of tree to be returned
	 * @param varTree tree to be substituted, must contain only one variable
	 * @param replaceTree one tree, can containing variables which shall be replaced for the variable
	 * @param tc a tree creator to produce the substituted tree
	 * @return a tree on which the only one variable is replaced by another tree, which can contain variables, too.
	 */
	public static <F extends RankedSymbol, 
	V extends Variable, 
	U extends Tree<BiSymbol<F,V>>> 
	U replaceOneVariable(Tree<? extends BiSymbol<F,V>> varTree, U replaceTree, TreeCreator<BiSymbol<F,V>,U> tc) {

		if (varTree == null){
			throw new NullPointerException("varTree is not there.");
		}
		if (getHighestVariableNumber(varTree) > 0){
			throw new IllegalArgumentException("varTree must only contain one variable.");
		}

		// if the symbol is an Variable, replace it by the given replacing tree
		if (varTree.getSymbol().isLeafType()) {
			return replaceTree;
		} 
		// else it is a function symbol
		// look in all subtrees for variables and replace them recursively
		else {
			List<? extends Tree<? extends BiSymbol<F,V>>> subs = varTree.getSubTrees();
			List<U> newsubs = new LinkedList<U>();
			// apply the function on the subtrees as long as all variables are reached an eliminated
			for (Tree<? extends BiSymbol<F,V>> sub: subs){
				newsubs.add(VarTreeOps.<F,V,U>replaceOneVariable(sub, replaceTree, tc));
			}
			// produce the tree
			return tc.makeTree(varTree.getSymbol(), newsubs);
		}
	}


	/**
	 * Replaces variables in a tree by a given list of trees - the indices of the
	 * list members correspond to the numbers of the variables to be replaced, i.e.
	 * if a variable with number i occurs in the variable tree, it is replaced by
	 * the i-th list member.
	 * 
	 * @param <F> type of function symbols occurring in the specified tree
	 * @param <V> type of variables occurring in the specified tree
	 * @param <U> type of tree to be returned
	 * @param varTree tree to be substituted
	 * @param replaceTrees the list of trees which shall replace the variables
	 * (i-th list member replaces variable with number i)
	 * @param tc a tree creator to produce the substituted tree
	 * @return a tree on which the variables are replaced by the trees specified in the given list
	 */
	public static <F extends RankedSymbol, 
	V extends Variable, 
	U extends Tree<F>> 
	U replaceVariables(Tree<BiSymbol<F,V>> varTree, Map<V,U> replaceTrees, TreeCreator<F,U> tc) {
		// if the symbol is an Variable, replace it by the according subtree
		if (varTree.getSymbol().isLeafType()) {
			V v = varTree.getSymbol().asLeafSymbol();
			if (!replaceTrees.containsKey(v)){
				throw new IllegalArgumentException("The given map for replacing trees does not contain this variable in the tree: " + v);
			} else
				return replaceTrees.get(varTree.getSymbol().asLeafSymbol());
		} 
		// else it is a function symbol
		// look in all subtrees for variables and replace them recursively
		else {
			F sf = varTree.getSymbol().asInnerSymbol();
			List<? extends Tree<BiSymbol<F,V>>> subs = varTree.getSubTrees();
			List<U> newsubs = new LinkedList<U>();
			// apply the function on the subtrees as long as all variables are reached an eliminated
			for (Tree<BiSymbol<F,V>> sub: subs){
				newsubs.add(VarTreeOps.<F,V,U>replaceVariables(sub, replaceTrees, tc));
			}
			// produce the tree
			return tc.makeTree(sf, newsubs);
		}
	}


	/**
	 * Checks whether a given variable tree is linear, i.e. each variable occurs at most once.
	 * 
	 * @param <F> type of function symbols occurring in the specified tree
	 * @param <V> type of variables occurring in the specified tree
	 * @param varTree tree to be analyzed
	 * @return true if the variable tree is linear, i.e. each variable occurs at most once,
	 * false otherwise
	 */
	public static <F extends RankedSymbol, V extends Variable> boolean isLinear(Tree<? extends BiSymbol<F,V>> varTree) {
		Set<Variable> usedVariables = new HashSet<Variable>();
		return !findDoubles(varTree, usedVariables);
	}


	/**
	 * Helper method for isLinear() - collects variables occurring in tree until a variable is found twice
	 * or until the whole tree has been traversed. The method checks if there are doubles, so returns true, 
	 * if there are any double occurrences of variables found.
	 * 
	 * @param <F> type of function symbols occurring in the specified tree
	 * @param <V> type of variables occurring in the specified tree
	 * @param varTree tree to be analyzed
	 * @param usedVariables which variables already have been found
	 * @return true if and only if the variable tree is linear, i.e. each variable occurs at most once,
	 */
	private static <F extends RankedSymbol, V extends Variable> boolean findDoubles(Tree<? extends BiSymbol<F,V>> varTree, Set<Variable> usedVariables){
		if (varTree.getSymbol().isLeafType()) {
			Variable v = varTree.getSymbol().asLeafSymbol();
			// if some variable is already there
			if (usedVariables.contains(v)){
				return true;
			} 
			// otherwise add it
			else {
				usedVariables.add(v);
			}
		} 
		// otherwise look in the subTrees
		else {
			for (Tree<? extends BiSymbol<F,V>> sub: varTree.getSubTrees()){
				if (VarTreeOps.<F,V>findDoubles(sub, usedVariables)){
					return true;
				}
			}
		}
		return false;
	}


	/**
	 * Converts a tree into a tree containig variables via a given map that maps 
	 * some constants to variables which shall occur in the new tree. <br>
	 * 
	 * @param <F> type of ranked symbols of the trees 
	 * @param <W> type of variables that shall occur in the destination tree
	 * @param <Y> type of the returning variable tree
	 * @param vTree tree which shall be converted
	 * @param map map which maps constants of the tree to variables
	 * @param tc tree creator for the destination variable trees
	 * @return a variable tree where some constants of the old tree are replaced by some variables 
	 * via the given map 
	 */
	public static <F extends RankedSymbol, 
	W extends Variable,
	Y extends Tree<BiSymbol<F,W>>>  
	Y makeTreeToBiTree(Tree<F> vTree,
			Map<F ,? extends W> map, TreeCreator<BiSymbol<F,W>,Y> tc) {
		F symbol = vTree.getSymbol();
		// if it is a variable search the corresponding variable and make a new tree
		if (map.containsKey(symbol)){
			if (symbol.getArity() != 0)
				throw new IllegalArgumentException("All symbols that shall be replaced must have arity 0.");
			W newVar = map.get(symbol);
			return tc.makeTree(new LeafSymbol<F,W>(newVar));
		} 
		// at the other hand, recursively convert the subtrees
		else {
			List<Y> subs = new LinkedList<Y>();
			for (Tree<F> sub: vTree.getSubTrees()){
				subs.add(makeTreeToBiTree(sub,map,tc));
			}
			return tc.makeTree(new InnerSymbol<F,W>(symbol), subs);
		}
	}

}
