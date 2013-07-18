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
	
	protected RedirectionTargetFinder(CodeChecker codeChecker) {
		this(codeChecker, RedirectionTargetFindingMethod.RandomStrongest);
	}
	
	protected RedirectionTargetFinder(CodeChecker codeChecker, RedirectionTargetFindingMethod findingStrategy) {
		this.codeChecker = codeChecker;
		this.findingStrategy = findingStrategy;
	}
	
	//FIXME
	protected HashMap <AnnotatedProgramPoint , HashSet <AnnotatedProgramPoint>> findReturnRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {
		return null;
	}
	
	//FIXME
	protected AnnotatedProgramPoint findReturnRedirectionCallPred(AnnotatedProgramPoint callPred, AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {
		return null;
	}

	protected AnnotatedProgramPoint findRedirectionTarget(
			AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {
		switch(findingStrategy) {
		case First:
			return findFirstRedirectionTarget(predecessorNode, dest);
		case FirstStrongest:
			return findFirstStrongestRedirectionTarget(predecessorNode, dest);
		case Random:
			return findRandomRedirectionTarget(predecessorNode, dest);
		case RandomStrongest:
			return findRandomStrongestRedirectionTarget(predecessorNode, dest);
		case Alex:
			return null; //FIXME // Alex : Write your redirection algorithm here.
		default:
			return null;
		}
	}

	private AnnotatedProgramPoint findFirstRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(dest);
		
		ArrayList <AnnotatedProgramPoint> candidates = dest.getNewCopies();
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(codeChecker.isValidEdge(predecessorNode, label, candidate)) {
				return candidate;
			}
		}
		
		return null;
		
	}
	
	private AnnotatedProgramPoint findFirstStrongestRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(dest);
		
		ArrayList <AnnotatedProgramPoint> candidates = dest.getNewCopies();
		
		AnnotatedProgramPoint target = null;
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(codeChecker.isValidEdge(predecessorNode, label, candidate)) {
				if(target == null || codeChecker.isStrongerPredicate(candidate, target))
					target = candidate;
			}
		}
		
		return target;
		
	}
	
	private AnnotatedProgramPoint findRandomRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(dest);
		
		ArrayList <AnnotatedProgramPoint> candidates = dest.getNewCopies();
		
		Collections.shuffle(candidates);
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(codeChecker.isValidEdge(predecessorNode, label, candidate)) {
				return candidate;
			}
		}
		
		return null;
		
	}
	
	private AnnotatedProgramPoint findRandomStrongestRedirectionTarget(AnnotatedProgramPoint predecessorNode, AnnotatedProgramPoint dest) {

		CodeBlock label = predecessorNode.getOutgoingEdgeLabel(dest);
		
		ArrayList <AnnotatedProgramPoint> candidates = dest.getNewCopies();
		
		Collections.shuffle(candidates);
		
		AnnotatedProgramPoint target = null;
		
		for (AnnotatedProgramPoint candidate : candidates) {
			if(codeChecker.isValidEdge(predecessorNode, label, candidate)) {
				if(target == null || codeChecker.isStrongerPredicate(candidate, target))
					target = candidate;
			}
		}
		
		return target;
		
	}
}
