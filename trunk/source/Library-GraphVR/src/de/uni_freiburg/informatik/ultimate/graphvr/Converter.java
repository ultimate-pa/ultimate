package de.uni_freiburg.informatik.ultimate.graphvr;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.graphvr.TraceAbstractionProtos.Result;
import de.uni_freiburg.informatik.ultimate.graphvr.TraceAbstractionProtos.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.graphvr.TraceAbstractionProtos.TAPreferences.Concurrency;
import de.uni_freiburg.informatik.ultimate.graphvr.TraceAbstractionProtos.TAPreferences.Format;
import de.uni_freiburg.informatik.ultimate.graphvr.TraceAbstractionProtos.TAPreferences.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.graphvr.TraceAbstractionProtos.TAPreferences.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.graphvr.TraceAbstractionProtos.TAPreferences.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.graphvr.TraceAbstractionProtos.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.graphvr.TraceAbstractionProtos.TAPreferences.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.graphvr.TraceAbstractionProtos.TAPreferences.Minimization;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

public class Converter {

	public static TraceAbstractionProtos.NestedWordAutomaton fromAutomaton(
			NestedWordAutomaton<CodeBlock, IPredicate> automaton) {
		return null;
	}

	public static TraceAbstractionProtos.Alphabet fromAlphabet(Set<CodeBlock> alphabet) {
		final TraceAbstractionProtos.Alphabet.Builder builder = TraceAbstractionProtos.Alphabet.newBuilder();
		for (CodeBlock codeBlock : alphabet) {
			builder.addLetter(fromCodeblock(codeBlock));
		}
		return builder.build();
	}

	private static TraceAbstractionProtos.StateSet fromStateSet(Set<IPredicate> stateset) {
		final TraceAbstractionProtos.StateSet.Builder builder = TraceAbstractionProtos.StateSet.newBuilder();
		for (IPredicate iPredicate : stateset) {
			builder.addState(fromPredicate(iPredicate));
		}
		return builder.build();
	}
	
	private static TraceAbstractionProtos.NestedWordAutomaton.transition fromTransition(
			Map<IPredicate, Map<CodeBlock, Set<IPredicate>>> transition) {
		final TraceAbstractionProtos.NestedWordAutomaton.transition.Builder builder =
				TraceAbstractionProtos.NestedWordAutomaton.transition.newBuilder();
		return builder.build();
	}

	public static TraceAbstractionProtos.CodeBlock fromCodeblock(CodeBlock codeblock) {
		return TraceAbstractionProtos.CodeBlock.newBuilder()
				.setCode(codeblock.getPrettyPrintedStatements())
				.build();
	}

	public static TraceAbstractionProtos.Predicate fromPredicate(IPredicate predicate) {
		return TraceAbstractionProtos.Predicate.newBuilder()
				.setLabel(predicate.toString())
				.build();
	}

	public static TraceAbstractionProtos.TAPreferences fromTAPreferences(TAPreferences preferences) {
		final InterpolantAutomatonEnhancement enhancment;
		switch (preferences.interpolantAutomatonEnhancement()) {
		case NONE:
			enhancment= InterpolantAutomatonEnhancement.NO_ENHANCEMENT;
			break;
		default:
			enhancment= InterpolantAutomatonEnhancement.valueOf(preferences.interpolantAutomatonEnhancement().name());
		}
		
		final Minimization minimization;
		switch (preferences.getMinimization()) {
		case NONE:
			minimization = Minimization.NO_MINIMIZATION;
			break;

		default:
			minimization = Minimization.valueOf(preferences.getMinimization().name());
			break;
		}
		
		return TraceAbstractionProtos.TAPreferences.newBuilder()
				.setMInterprocedural(preferences.interprocedural())
				.setMMaxIterations(preferences.maxIterations())
				.setMWatchIteration(preferences.watchIteration())
				.setMArtifact(Artifact.valueOf(preferences.artifact().name()))
				.setMInterpolation(InterpolationTechnique.valueOf(preferences.interpolation().name()))
				.setMInterpolantAutomaton(InterpolantAutomaton.valueOf(preferences.interpolantAutomaton().name()))
				.setMDumpAutomata(preferences.dumpAutomata())
				.setMAutomataFormat(Format.valueOf(preferences.getAutomataFormat().name()))
				.setMDumpPath(preferences.dumpPath())
				.setMDeterminiation(enhancment)
				.setMMinimize(minimization)
				.setMHoare(preferences.computeHoareAnnotation())
				.setMConcurrency(Concurrency.valueOf(preferences.getConcurrency().name()))
				.setMHoareTripleChecks(HoareTripleChecks.valueOf(preferences.getHoareTripleChecks().name()))
				.setMHoareAnnotationPositions(HoareAnnotationPositions.valueOf(preferences.getHoareAnnotationPositions().name()))
				.build();
	}

	public static TraceAbstractionProtos.Result fromResult(AbstractCegarLoop.Result result) {
		return Result.valueOf(result.name());
//		switch (result) {
//		case SAFE:
//			return Result.SAFE;
//		case TIMEOUT:
//			return Result.TIMEOUT;
//		case UNKNOWN:
//			return Result.UNKNOWN;
//		case UNSAFE:
//			return Result.UNSAFE;
//		default:
//			return null;
//		}
	}
	
}