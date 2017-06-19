/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Mohamed Sherif
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CodeCheck plug-in.
 * 
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.impulse;

import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeChecker;

/**
 * Specifies the algorithm for finding the redirection target.
 *
 * @author Mohamed Sherif
 */
enum RedirectionTargetFindingMethod {
	/**
	* finds the first valid redirection target
	*/
	First, 
	/**
	* finds the first valid redirection target, and then goes on to find if other valid targets are stronger
	*/
	FirstStrongest, 
	/**
	* shuffles the list of candidates, then finds the first valid redirection target
	*/
	Random, 
	/**
	* shuffles the list of candidates, finds the first valid redirection target, then tries to find stronger ones
	*/
	RandomStrongest, 
	/**
	* left for alex to implement his own method
	*/
	Alex
}

/**
 * A class having several ways and algorithms dedicated to finding the best redirection target of an old edge.
 *
 * @author Mohamed Sherif
 */
public class RedirectionTargetFinder {
	
	private CodeChecker codeChecker;
	private RedirectionTargetFindingMethod findingStrategy;
	private boolean random;

	/**
	 * Constructor of a new Finder.
	 * @param codeChecker the code checker that uses this finder
	 * @param findingStrategy specifies which finding algorithm will be used
	 * @see RedirectionTargetFindingMethod
	 *
	protected RedirectionTargetFinder(CodeChecker codeChecker, RedirectionTargetFindingMethod findingStrategy) {
		this.codeChecker = codeChecker;
		this.findingStrategy = findingStrategy;
		if(findingStrategy == RedirectionTargetFindingMethod.Random || findingStrategy == RedirectionTargetFindingMethod.RandomStrongest)
			random = true;
		else
			random = false;
	}
	
	/**
	 * Constructor of a new Finder with RandomStrongest as the default finding strategy.
	 * @param codeChecker the code checker that uses this finder
	 * @see RedirectionTargetFindingMethod
	 *
	protected RedirectionTargetFinder(CodeChecker codeChecker) {
		this(codeChecker, RedirectionTargetFindingMethod.RandomStrongest);
	}

	/**
	 * Finds an edge redirection target according to the specified finding method.
	 * @param predecessorNode the source of the old edge
	 * @param dest the destination of the old edge
	 * @return returns a new destination, returns null if no valid destination is found
	 *
	protected AnnotatedProgramPoint findRedirectionTarget(
			AppEdge edge) {
//			AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {
		switch(findingStrategy) {
		case First:
		case Random:
			return findFirstRedirectionTarget(edge);
		case FirstStrongest:
		case RandomStrongest:
			return findStrongestRedirectionTarget(edge);
		case Alex:
			return null; // Alex : Write your redirection algorithm here.
		default:
			return null;
		}
	}
	
	/**
	 * Finds a hyper edge redirection target according to the specified finding method.
	 * @param predecessorNode the source of the old hyper edge
	 * @param callPred the call predecessor of the old hyper edge
	 * @param dest the destination of the old edge
	 * @return returns a new destination, returns null if no valid destination is found
	 *
	protected AnnotatedProgramPoint findReturnRedirectionTarget(
			AnnotatedProgramPoint predecessorNode, 
			AnnotatedProgramPoint callPred, 
			AnnotatedProgramPoint dest) {

		switch(findingStrategy) {
		case First:
		case Random:
			return findFirstReturnRedirectionTarget(predecessorNode, callPred, dest);
		case FirstStrongest:
		case RandomStrongest:
			return findStrongestReturnRedirectionTarget(predecessorNode, callPred, dest);
		case Alex:
			return null; // Alex : Write your redirection algorithm here.
		default:
			return null;
		}
	}

	/**
	 * Finds an edge redirection target according to the specified finding method.
	 * @param predecessorNode the source of the old edge
	 * @param dest the destination of the old edge
	 * @return returns a new destination, returns null if no valid destination is found
	 * @see #findRedirectionTarget(AnnotatedProgramPoint, AnnotatedProgramPoint)
	 * @see RedirectionTargetFindingMethod#First
	 * @see RedirectionTargetFindingMethod#Random
	 *
	private AnnotatedProgramPoint findFirstRedirectionTarget(AppEdge edge) {
//			AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {

//		IIcfgTransition<?> label = predecessorNode.getOutgoingEdgeLabel(dest);
		IIcfgTransition<?> label = edge.getStatement();
		
		ArrayList <AnnotatedProgramPoint> candidates = edge.getTarget().getNewCopies();

		if(random)
			Collections.shuffle(candidates);
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(codeChecker.isValidEdge(edge.getSource(), label, candidate)) {
				return candidate;
			}
		}
		
		return null;
		
	}

	/**
	 * Finds an edge redirection target according to the specified finding method.
	 * @param predecessorNode the source of the old edge
	 * @param dest the destination of the old edge
	 * @return returns a new destination, returns null if no valid destination is found
	 * @see #findRedirectionTarget(AnnotatedProgramPoint, AnnotatedProgramPoint)
	 * @see RedirectionTargetFindingMethod#FirstStrongest
	 * @see RedirectionTargetFindingMethod#RandomStrongest
	 *
	private AnnotatedProgramPoint findStrongestRedirectionTarget(AppEdge edge) {
//			AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {

//		IIcfgTransition<?> label = predecessorNode.getOutgoingEdgeLabel(dest); 
		
		
		ArrayList <AnnotatedProgramPoint> candidates = edge.getTarget().getNewCopies();
		
		if(random)
			Collections.shuffle(candidates);

		AnnotatedProgramPoint res = null;
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(codeChecker.isValidEdge(edge.getSource(), edge.getStatement(), candidate)) {
				if(res == null || codeChecker.isStrongerPredicate(candidate, res))
					res = candidate;
			}
		}
		
		return res;
	}

	/**
	 * Finds a hyper edge redirection target according to the specified finding method.
	 * @param predecessorNode the source of the old hyper edge
	 * @param callPred the call predecessor of the old hyper edge
	 * @param dest the destination of the old edge
	 * @return returns a new destination, returns null if no valid destination is found
	 * @see #findReturnRedirectionTarget(AnnotatedProgramPoint, AnnotatedProgramPoint, AnnotatedProgramPoint)
	 * @see RedirectionTargetFindingMethod#First
	 * @see RedirectionTargetFindingMethod#Random
	 *
	private AnnotatedProgramPoint findFirstReturnRedirectionTarget(
			AnnotatedProgramPoint predecessorNode, 
			AnnotatedProgramPoint callPred, 
			AnnotatedProgramPoint dest) {

//		IIcfgTransition<?> label = predecessorNode.getOutgoingEdgeLabel(dest);
//		
//		ArrayList <AnnotatedProgramPoint> candidates = dest.getNewCopies();
//
//		if(random)
//			Collections.shuffle(candidates);
//		
//		for (AnnotatedProgramPoint candidate : candidates) {
//			if(codeChecker.isValidReturnEdge(predecessorNode, label, candidate, callPred)) {
//				return candidate;
//			}
//		}
		
		return null;
	}

	/**
	 * Finds an edge redirection target according to the specified finding method.
	 * @param predecessorNode the source of the old hyper edge
	 * @param callPred the call predecessor of the old hyper edge
	 * @param dest the destination of the old edge
	 * @return returns a new destination, returns null if no valid destination is found
	 * @see #findReturnRedirectionTarget(AnnotatedProgramPoint, AnnotatedProgramPoint, AnnotatedProgramPoint)
	 * @see RedirectionTargetFindingMethod#FirstStrongest
	 * @see RedirectionTargetFindingMethod#RandomStrongest
	 *
	private AnnotatedProgramPoint findStrongestReturnRedirectionTarget(
			AnnotatedProgramPoint predecessorNode, 
			AnnotatedProgramPoint callPred, 
			AnnotatedProgramPoint dest) {

//		IIcfgTransition<?> label = predecessorNode.getOutgoingEdgeLabel(dest);//FIXME
//		
//		ArrayList <AnnotatedProgramPoint> candidates = dest.getNewCopies();
//
//		if(random)
//			Collections.shuffle(candidates);
//		
//		AnnotatedProgramPoint res = null;
//
//		for (AnnotatedProgramPoint candidate : candidates) {
//			if(codeChecker.isValidReturnEdge(predecessorNode, label, candidate, callPred)) {
//				if(res == null || codeChecker.isStrongerPredicate(candidate, res))
//					res = candidate;
//			}
//		}
//		
//		return res;
		return null;
	}
	*/
}
