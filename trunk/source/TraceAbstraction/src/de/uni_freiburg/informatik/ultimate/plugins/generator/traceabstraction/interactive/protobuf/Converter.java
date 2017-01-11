package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.protobuf;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.protobuf.TraceAbstractionProtos;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.protobuf.TraceAbstractionProtos.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.protobuf.TraceAbstractionProtos.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.protobuf.TraceAbstractionProtos.TAPreferences.Concurrency;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.protobuf.TraceAbstractionProtos.TAPreferences.Format;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.protobuf.TraceAbstractionProtos.TAPreferences.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.protobuf.TraceAbstractionProtos.TAPreferences.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.protobuf.TraceAbstractionProtos.TAPreferences.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.protobuf.TraceAbstractionProtos.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.protobuf.TraceAbstractionProtos.TAPreferences.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.protobuf.TraceAbstractionProtos.TAPreferences.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class Converter {

	public static TraceAbstractionProtos.IterationInfo.NestedRun fromNestedRun(IRun<CodeBlock, IPredicate, ?> run) {
		TraceAbstractionProtos.IterationInfo.NestedRun.Builder builder = TraceAbstractionProtos.IterationInfo.NestedRun
				.newBuilder();
		run.getWord().asList().stream().map(Converter::fromCodeblock).forEach(builder::addNestedWord);
		// builder.addAllNestedWord(values)
		return builder.build();
	}

	public static TraceAbstractionProtos.NestedWordAutomaton fromAutomaton(
			INestedWordAutomaton<CodeBlock, IPredicate> automaton) {
		final List<CodeBlock> callAlphabet = new ArrayList<>();
		automaton.getCallAlphabet().forEach(callAlphabet::add);
		final List<CodeBlock> internalAlphabet = new ArrayList<>();
		automaton.getInternalAlphabet().forEach(internalAlphabet::add);
		final List<CodeBlock> returnAlphabet = new ArrayList<>();
		automaton.getReturnAlphabet().forEach(returnAlphabet::add);
		final List<IPredicate> states = new ArrayList<>();
		automaton.getStates().forEach(states::add);
		final Function<Consumer<Integer>, Consumer<IPredicate>> addStateRef = addRef(states);

		final TraceAbstractionProtos.NestedWordAutomaton.Builder builder = TraceAbstractionProtos.NestedWordAutomaton
				.newBuilder();

		builder.setCall(fromAlphabet(callAlphabet)).setInternal(fromAlphabet(internalAlphabet))
				.setReturn(fromAlphabet(returnAlphabet));

		addStateRef.apply(builder::setEmptyStack).accept(automaton.getEmptyStackState());

		for (IPredicate state : states) {
			builder.addStates(fromPredicate(state));
			if (automaton.isInitial(state))
				addStateRef.apply(builder::addInitial).accept(state);
			if (automaton.isFinal(state))
				addStateRef.apply(builder::addFinal).accept(state);

			stream(automaton.internalSuccessors(state)).map(getTransition(state, internalAlphabet, states))
					.forEach(builder::addInternalEdges);
			stream(automaton.callSuccessors(state)).map(getTransition(state, callAlphabet, states))
					.forEach(builder::addCallEdges);
			stream(automaton.returnSuccessors(state)).map(getTransition(state, returnAlphabet, states))
					.forEach(builder::addReturnEdges);
		}
		// states.stream()
		// .map(Converter::fromPredicate)
		// .forEach(builder::addStates);

		// .setCallIn(fromTransition(automaton.callPredecessors(succ),
		// states, alphabet))
		//
		// automaton.getInitialStates().forEach(addStateRef.apply(builder::addInitial));
		// automaton.getFinalStates().forEach(addStateRef.apply(builder::addFinal));

		return builder.build();
	}

	private static <T> Stream<T> stream(Iterable<T> source) {
		return StreamSupport.stream(source.spliterator(), false);
	}

	private static Function<IOutgoingTransitionlet<CodeBlock, IPredicate>, TraceAbstractionProtos.NestedWordAutomaton.transition.Builder> getTransition(
			final IPredicate origin, List<CodeBlock> alphabet, List<IPredicate> states) {
		return transition -> {
			final TraceAbstractionProtos.NestedWordAutomaton.transition.Builder builder = TraceAbstractionProtos.NestedWordAutomaton.transition
					.newBuilder();
			addRef(states).apply(builder::setOriginState).accept(origin);
			addRef(states).apply(builder::setSuccessorState).accept(transition.getSucc());
			addRef(alphabet).apply(builder::setLetter).accept(transition.getLetter());
			return builder;
		};
	}

	private static <T> Function<Consumer<Integer>, Consumer<T>> addRef(final List<T> targets) {
		return action -> {
			return new Consumer<T>() {
				@Override
				public void accept(final T t) {
					action.accept(targets.indexOf(t));
				}
			};
		};
	}

	private static TraceAbstractionProtos.Alphabet fromAlphabet(Iterable<CodeBlock> alphabet) {
		final TraceAbstractionProtos.Alphabet.Builder builder = TraceAbstractionProtos.Alphabet.newBuilder();
		for (CodeBlock codeBlock : alphabet) {
			builder.addLetter(fromCodeblock(codeBlock));
		}
		return builder.build();
	}

	private static TraceAbstractionProtos.NestedWordAutomaton.transition fromTransition(
			Map<IPredicate, Map<CodeBlock, Set<IPredicate>>> transitions, List<IPredicate> states,
			List<CodeBlock> alphabet) {
		final TraceAbstractionProtos.NestedWordAutomaton.transition.Builder builder = TraceAbstractionProtos.NestedWordAutomaton.transition
				.newBuilder();
		for (Map.Entry<IPredicate, Map<CodeBlock, Set<IPredicate>>> transition : transitions.entrySet()) {
			final int firstIndex = states.indexOf(transition.getKey());
		}
		return builder.build();
	}

	public static TraceAbstractionProtos.CodeBlock fromCodeblock(CodeBlock codeblock) {
		return TraceAbstractionProtos.CodeBlock.newBuilder().setCode(codeblock.getPrettyPrintedStatements()).build();
	}

	public static TraceAbstractionProtos.Predicate fromPredicate(IPredicate predicate) {
		return TraceAbstractionProtos.Predicate.newBuilder().setLabel(predicate.toString()).build();
	}

	public static TraceAbstractionProtos.TAPreferences fromTAPreferences(TAPreferences preferences) {
		final InterpolantAutomatonEnhancement enhancment;
		switch (preferences.interpolantAutomatonEnhancement()) {
		case NONE:
			enhancment = InterpolantAutomatonEnhancement.NO_ENHANCEMENT;
			break;
		default:
			enhancment = InterpolantAutomatonEnhancement.valueOf(preferences.interpolantAutomatonEnhancement().name());
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

		return TraceAbstractionProtos.TAPreferences.newBuilder().setMInterprocedural(preferences.interprocedural())
				.setMMaxIterations(preferences.maxIterations()).setMWatchIteration(preferences.watchIteration())
				.setMArtifact(Artifact.valueOf(preferences.artifact().name()))
				.setMInterpolation(InterpolationTechnique.valueOf(preferences.interpolation().name()))
				.setMInterpolantAutomaton(InterpolantAutomaton.valueOf(preferences.interpolantAutomaton().name()))
				.setMDumpAutomata(preferences.dumpAutomata())
				.setMAutomataFormat(Format.valueOf(preferences.getAutomataFormat().name()))
				.setMDumpPath(preferences.dumpPath()).setMDeterminiation(enhancment).setMMinimize(minimization)
				.setMHoare(preferences.computeHoareAnnotation())
				.setMConcurrency(Concurrency.valueOf(preferences.getConcurrency().name()))
				.setMHoareTripleChecks(HoareTripleChecks.valueOf(preferences.getHoareTripleChecks().name()))
				.setMHoareAnnotationPositions(
						HoareAnnotationPositions.valueOf(preferences.getHoareAnnotationPositions().name()))
				.build();
	}

	public static TraceAbstractionProtos.Result fromResult(AbstractCegarLoop.Result result) {
		return Result.valueOf(result.name());
	}

}