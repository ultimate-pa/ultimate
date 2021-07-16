/*
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 * */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Constructs a Hitting set of from the collections of sets. @TODO: finish description, redundant?
 *
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <T>
 *           
 */

public class HittingSet <T>{
	private final Set<Set<T>> mCollection;
	
	
	public HittingSet(final Set<Set<T>> collection) {
		mCollection = collection;
		
	}
	
	/**
	 * 
	 * @param hittingSet
	 * @param setUniverse
	 * @return true if hittinSet intersects with all sets in setUniverse
	 */
	private boolean checkHittingSet(Set<T> hittingSet, Set<Set<T>> setUniverse) {
		Set<Set<T>> universe = new HashSet<Set<T>>(setUniverse);
		for (Set<T> set : universe) {
			if (DataStructureUtils.intersection(set, hittingSet).isEmpty()) {
				return false;
			}			
		}		
		return true;
	}
	
	
	/**
	 * @param s1
	 * @param s2
	 * @return Symmetric difference of set
	 * TODO:Already implemented in Ultimate? Guava library?
	 */
	private Set<T> getSymmDiff(Set<T> s1, Set<T> s2){
		Set<T> symmetricDiff = new HashSet<T>(s1);
	    symmetricDiff.addAll(s2);
	    Set<T> tmp = new HashSet<T>(s1);
	    tmp.retainAll(s2);
	    symmetricDiff.removeAll(tmp); // use DataStructre.difference??
	    return symmetricDiff;
	}
	
	/**
	 * @param collection of set
	 * @return set of symmetric differences of all set pairs in collection
	 */
	private Set<Set<T>> getSymmDifferences(Set<Set<T>> collection){
		 Set<Set<T>> differences= new HashSet<>();
		 Set<Set<T>> toCombine= new HashSet<>();
		 toCombine.addAll(collection);
		 for (Set<T> e: collection) {
			if (!toCombine.isEmpty()) {
				toCombine.remove(e);
				 for (Set<T> s :toCombine) {
					 differences.add(getSymmDiff(e,s));
				 }
			}
		 }
		 return differences;
	}
	
	/**
	 * 
	 * @param element
	 * @param collection
	 * @return List of sets that contains the element
	 */
	private Set<Set<T>> getIntersections(T element, Set<Set<T>> collection){
		Set<Set<T>> intersections = new HashSet<Set<T>>();
		for (Set<T> set : collection) {
			if(set.contains(element)) {
				intersections.add(set);
			}
		}
		return intersections;
	}
	
	
	/**
	 * 
	 * @param set 
	 * @param collection of not covered sets
	 * @return return set in uncovered
	 */
	private T getGreedyElement(Set<T> set, Set<Set<T>> collection) {
		
		Set<Set<T>> intersections = new HashSet<Set<T>>();
		T greedy = set.iterator().next();
		for (T element : set) {			
			Set<Set<T>> setInter = getIntersections(element,collection); 
			if ( setInter.size() > intersections.size()) {
				greedy = element;
				intersections = setInter;				
			}
		}
		return greedy;		
	}
	
	/**	
	 * 
	 * @param symmDifference
	 * @return hitting set of symmetricDifference
	 */
	private Set<T> getHittingSet(Set<Set<T>> collection) {
		Set<T> hittingSet = new HashSet<T>();
		Set<Set<T>> uncovered = new HashSet<Set<T>>();
		uncovered.addAll(collection);
		for (Set<T> set : collection) {			
			if (!checkHittingSet(hittingSet,collection)) {
				T greedy = getGreedyElement(set,uncovered);
				hittingSet.add(greedy);
				Set<Set<T>> inter = getIntersections(greedy, uncovered);
				uncovered = DataStructureUtils.difference(uncovered, inter);
			 }
			else {
				break;
			}
		}
		
		assert checkHittingSet(hittingSet,collection): "Error in Hitting set";
		return hittingSet;
	}
	
	public Set<T> getSymmHittingSet() {
		Set<Set<T>> collection = getSymmDifferences(mCollection);
		return getHittingSet(collection);
	}
	
	public Set<T> getHittingSet(){
		return getHittingSet(mCollection); 
	}
	
	
}









