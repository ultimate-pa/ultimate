package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;


enum RedirectionTargetFindingMethod {
	First, FirstStrongest, Random, RandomStrongest, Alex
}

public class RedirectionTargetFinder {
	
	private CodeChecker codeChecker;
	private RedirectionTargetFindingMethod findingStrategy;
	private boolean random;
	
	protected RedirectionTargetFinder(CodeChecker codeChecker) {
		this(codeChecker, RedirectionTargetFindingMethod.RandomStrongest);
	}
	
	protected RedirectionTargetFinder(CodeChecker codeChecker, RedirectionTargetFindingMethod findingStrategy) {
		this.codeChecker = codeChecker;
		this.findingStrategy = findingStrategy;
		if(findingStrategy == RedirectionTargetFindingMethod.Random || findingStrategy == RedirectionTargetFindingMethod.RandomStrongest)
			random = true;
		else
			random = false;
	}
	
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
	
	protected AnnotatedProgramPoint findReturnRedirectionCallPred(AnnotatedProgramPoint callPred, AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {
		switch(findingStrategy) {
		case First:
		case Random:
			return findFirstReturnRedirectionCallPred(callPred, predecessorNode, dest);
		case FirstStrongest:
		case RandomStrongest:
			return findStrongestReturnRedirectionCallPred(callPred, predecessorNode, dest);
		case Alex:
			return null; // Alex : Write your redirection algorithm here.
		default:
			return null;
		}
	}

	protected AnnotatedProgramPoint findRedirectionTarget(
			AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {
		switch(findingStrategy) {
		case First:
		case Random:
			return findFirstRedirectionTarget(predecessorNode, dest);
		case FirstStrongest:
		case RandomStrongest:
			return findStrongestRedirectionTarget(predecessorNode, dest);
		case Alex:
			return null; // Alex : Write your redirection algorithm here.
		default:
			return null;
		}
	}

	private AnnotatedProgramPoint findFirstRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(dest);
		
		ArrayList <AnnotatedProgramPoint> candidates = dest.getNewCopies();

		if(random)
			Collections.shuffle(candidates);
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(codeChecker.isValidEdge(predecessorNode, label, candidate)) {
				return candidate;
			}
		}
		
		return null;
		
	}
	
	private AnnotatedProgramPoint findStrongestRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(dest);
		
		ArrayList <AnnotatedProgramPoint> candidates = dest.getNewCopies();
		
		if(random)
			Collections.shuffle(candidates);

		AnnotatedProgramPoint res = null;
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(codeChecker.isValidEdge(predecessorNode, label, candidate)) {
				if(res == null || codeChecker.isStrongerPredicate(candidate, res))
					res = candidate;
			}
		}
		
		return res;
		
	}
	
	private AnnotatedProgramPoint findFirstReturnRedirectionCallPred(AnnotatedProgramPoint callPred, AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {
		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(dest);
		
		ArrayList <AnnotatedProgramPoint> candidates = callPred.getNewCopies();

		if(random)
			Collections.shuffle(candidates);
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(codeChecker.isValidReturnEdge(predecessorNode, label, dest, candidate)) {
				return candidate;
			}
		}
		
		return null;
	}

	private AnnotatedProgramPoint findStrongestReturnRedirectionCallPred(AnnotatedProgramPoint callPred, AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {
		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(dest);
		
		ArrayList <AnnotatedProgramPoint> candidates = callPred.getNewCopies();

		if(random)
			Collections.shuffle(candidates);

		AnnotatedProgramPoint res = null;
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(codeChecker.isValidReturnEdge(predecessorNode, label, dest, candidate)) {
				if(res == null || codeChecker.isStrongerPredicate(candidate, res))
					res = candidate;
			}
		}
		
		return res;
	}

	private AnnotatedProgramPoint findFirstReturnRedirectionTarget(
			AnnotatedProgramPoint predecessorNode, 
			AnnotatedProgramPoint callPred, 
			AnnotatedProgramPoint dest) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(dest);
		
		ArrayList <AnnotatedProgramPoint> candidates = dest.getNewCopies();

		if(random)
			Collections.shuffle(candidates);
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(codeChecker.isValidReturnEdge(predecessorNode, label, candidate, callPred)) {
				return candidate;
			}
		}
		
		return null;
	}

	private AnnotatedProgramPoint findStrongestReturnRedirectionTarget(
			AnnotatedProgramPoint predecessorNode, 
			AnnotatedProgramPoint callPred, 
			AnnotatedProgramPoint dest) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(dest);
		
		ArrayList <AnnotatedProgramPoint> candidates = dest.getNewCopies();

		if(random)
			Collections.shuffle(candidates);
		
		AnnotatedProgramPoint res = null;

		for (AnnotatedProgramPoint candidate : candidates) {
			if(codeChecker.isValidReturnEdge(predecessorNode, label, candidate, callPred)) {
				if(res == null || codeChecker.isStrongerPredicate(candidate, res))
					res = candidate;
			}
		}
		
		return res;
	}
}