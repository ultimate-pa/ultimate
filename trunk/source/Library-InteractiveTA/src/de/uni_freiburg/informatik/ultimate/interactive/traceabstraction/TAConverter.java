package de.uni_freiburg.informatik.ultimate.interactive.traceabstraction;

import java.lang.reflect.Field;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;
import java.util.stream.Collectors;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.Converter;
import de.uni_freiburg.informatik.ultimate.interactive.conversion.ConverterRegistry;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.InteractiveIterationInfo;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.InterpolantsPrePost;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.LivePreferences;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.Message;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.NestingRelation;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.PredicateDoubleDecker;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.Result;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.Strategy;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.TAPreferences.Artifact;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.TAPreferences.Concurrency;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.TAPreferences.Format;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.TAPreferences.HoareAnnotationPositions;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.TAPreferences.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.TAPreferences.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.TAPreferences.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.interactive.traceabstraction.protobuf.TraceAbstractionProtos.TAPreferences.Minimization;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarStatisticsType.SizeIterationPair;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.InteractiveLive;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.InterpolantSequences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.IterationInfo;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.IterationInfo.Info;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.PreNestedWord;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.PreNestedWord.Loop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.MultiTrackTraceAbstractionRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.MultiTrackTraceAbstractionRefinementStrategy.Track;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.interactive.ParrotInteractiveIterationInfo;
import de.uni_freiburg.informatik.ultimate.util.HistogramOfIterable;

public class TAConverter extends Converter<GeneratedMessageV3, Object> {
	public TAConverter(IUltimateServiceProvider services) {
		super(services, Object.class);
	}

	@Override
	protected void init(ConverterRegistry<GeneratedMessageV3, Object> converterRegistry) {
		converterRegistry.registerBA(TraceAbstractionProtos.NestedRun.class, NestedRun.class,
				TAConverter::fromNestedRun);
		converterRegistry.registerAB(TraceAbstractionProtos.PreNestedWord.class, PreNestedWord.class,
				this::toPreNestedWord);
		// converterRegistry.registerAB(TraceAbstractionProtos.NestedWord.class, PreNestedWord.class,
		// TAConverter::nwToPreNestedWord);
		// converterRegistry.registerAB(TraceAbstractionProtos.NestedRun.class, NestedRun.class,
		// TAConverter::toNestedRun);
		// converterRegistry.registerAB(TraceAbstractionProtos.NestedWord.class, NestedWord.class,
		// TAConverter::toNestedWord);
		@SuppressWarnings("unchecked")
		Class<INestedWordAutomaton<CodeBlock, IPredicate>> cls =
				(Class<INestedWordAutomaton<CodeBlock, IPredicate>>) (Class) INestedWordAutomaton.class;
		converterRegistry.registerBA(TraceAbstractionProtos.NestedWordAutomaton.class, cls, TAConverter::fromAutomaton);
		Class<INestedWordAutomatonSimple<CodeBlock, IPredicate>> scls =
				(Class<INestedWordAutomatonSimple<CodeBlock, IPredicate>>) (Class) INestedWordAutomatonSimple.class;
		converterRegistry.registerBA(TraceAbstractionProtos.NestedWordAutomaton.class, scls,
				TAConverter::fromSimpleAutomaton);
		converterRegistry.registerBA(TraceAbstractionProtos.TAPreferences.class, TAPreferences.class,
				TAConverter::fromTAPreferences);
		converterRegistry.registerBA(TraceAbstractionProtos.CegarResult.class, AbstractCegarLoop.Result.class,
				TAConverter::fromResult);

		converterRegistry.registerAB(TraceAbstractionProtos.Question.class, Boolean.class,
				TraceAbstractionProtos.Question::getAnswer);
		converterRegistry.registerBA(TraceAbstractionProtos.Message.class, String.class, TAConverter::fromMessage);

		converterRegistry.registerAB(TraceAbstractionProtos.Tracks.class,
				MultiTrackTraceAbstractionRefinementStrategy.Track[].class, TAConverter::toTracks);
		converterRegistry.registerBA(TraceAbstractionProtos.Tracks.class,
				MultiTrackTraceAbstractionRefinementStrategy.Track[].class, TAConverter::fromTracks);
		converterRegistry.registerAB(InteractiveIterationInfo.class, ParrotInteractiveIterationInfo.class,
				TAConverter::toIterationInfo);
		converterRegistry.registerBA(InteractiveIterationInfo.class, ParrotInteractiveIterationInfo.class,
				TAConverter::fromIterationInfo);

		converterRegistry.registerBA(TraceAbstractionProtos.IterationInfo.class, IterationInfo.Info.class,
				TAConverter::fromIterationInfo);
		converterRegistry.registerBA(TraceAbstractionProtos.TraceHistogram.class, HistogramOfIterable.class,
				TAConverter::fromHistogram);

		converterRegistry.registerBA(TraceAbstractionProtos.InterpolantSequences.class, InterpolantSequences.class,
				TAConverter::fromInterpolants);

		converterRegistry.registerAB(TraceAbstractionProtos.LivePreferences.class, InteractiveLive.Preferences.class,
				TAConverter::toLivePreferences);

		converterRegistry.registerRConv(TraceAbstractionProtos.InterpolantSequences.Choices.class,
				InterpolantSequences.class, InterpolantSequences.class, TAConverter::getInterpolantSequences);
	}

	private static InterpolantSequences getInterpolantSequences(
			TraceAbstractionProtos.InterpolantSequences.Choices choices, InterpolantSequences originalSequences) {
		final List<InterpolantsPreconditionPostcondition> newPerfectIpps =
				choices.getPerfectList().stream().map(originalSequences.mPerfectIpps::get).collect(Collectors.toList());
		final List<InterpolantsPreconditionPostcondition> newImperfectIpps = choices.getImperfectList().stream()
				.map(originalSequences.mImperfectIpps::get).collect(Collectors.toList());
		return new InterpolantSequences().set(newPerfectIpps, newImperfectIpps);
	}

	private static InteractiveLive.Preferences toLivePreferences(LivePreferences prefs) {
		return new InteractiveLive.Preferences(prefs.getCEXS(), prefs.getIPS(), prefs.getRSS(), prefs.getPaused());
	}

	private static TraceAbstractionProtos.InterpolantSequences
			fromInterpolants(final InterpolantSequences interpolants) {
		final TraceAbstractionProtos.InterpolantSequences.Builder builder =
				TraceAbstractionProtos.InterpolantSequences.newBuilder();

		interpolants.mPerfectIpps.stream().map(TAConverter::fromIPP).forEach(builder::addPerfect);
		interpolants.mImperfectIpps.stream().map(TAConverter::fromIPP).forEach(builder::addImperfect);

		return builder.build();
	}

	private static TraceAbstractionProtos.InterpolantsPrePost fromIPP(final InterpolantsPreconditionPostcondition ipp) {
		final InterpolantsPrePost.Builder builder = InterpolantsPrePost.newBuilder();
		builder.setPreCondition(fromPredicate(ipp.getPrecondition()))
				.setPostCondition(fromPredicate(ipp.getPostcondition()));
		ipp.getInterpolants().stream().map(TAConverter::fromPredicate).forEach(builder::addInterpolants);
		return builder.build();
	}

	private static Message fromMessage(final String message) {
		final String[] msgs = message.split(":");
		final String title, subtitle, text;
		text = msgs.length > 0 ? msgs[msgs.length - 1] : "Empty Message";
		title = msgs.length > 1 ? msgs[0] : "Message";
		subtitle = msgs.length > 2 ? msgs[1] : "";

		return Message.newBuilder().setTitle(title).setSubtitle(subtitle).setText(text).build();
	}

	private static Loop toLoop(TraceAbstractionProtos.PreNestedWord.Loop loop) {
		return new Loop(loop.getStartPosition(), loop.getEndPosition(), loop.getRepetitions());
	}

	private PreNestedWord toPreNestedWord(TraceAbstractionProtos.PreNestedWord preNestedWord) {
		NestingRelation nr = preNestedWord.getNestingRelation();
		List<Loop> loops = new ArrayList<>();
		TraceAbstractionProtos.PreNestedWord.Loop[] protoloops =
				new TraceAbstractionProtos.PreNestedWord.Loop[preNestedWord.getLoopList().size()];
		preNestedWord.getLoopList().toArray(protoloops);
		Arrays.sort(protoloops, LoopComparator);
		Arrays.stream(protoloops).map(TAConverter::toLoop).forEach(l -> Loop.addLoop(loops, l));
		return new PreNestedWord(getServices().getLoggingService().getLogger(PreNestedWord.class),
				preNestedWord.getSymbolList(), nr.getPendingCallList(), nr.getPendingReturnList(),
				nr.getInternalNestingMap(), loops);
	}

	private static Comparator<TraceAbstractionProtos.PreNestedWord.Loop> LoopComparator =
			new Comparator<TraceAbstractionProtos.PreNestedWord.Loop>() {
				@Override
				public int compare(TraceAbstractionProtos.PreNestedWord.Loop o1,
						TraceAbstractionProtos.PreNestedWord.Loop o2) {
					final int cmp = Integer.compare(o1.getStartPosition(), o2.getStartPosition());
					if (cmp != 0)
						return cmp;
					// We want outer loops first - thus if the starting point matches
					// we want loops with bigger endpoints first
					return Integer.compare(o2.getEndPosition(), o1.getEndPosition());
				}
			};

	private static TraceAbstractionProtos.TraceHistogram fromHistogram(HistogramOfIterable<CodeBlock> histogram) {
		TraceAbstractionProtos.TraceHistogram.Builder builder = TraceAbstractionProtos.TraceHistogram.newBuilder();

		Field f;
		try {
			f = histogram.getClass().getDeclaredField("mHistogramMap");
			f.setAccessible(true);
			@SuppressWarnings("unchecked")
			Map<CodeBlock, Integer> histogramMap = (Map<CodeBlock, Integer>) f.get(histogram); // IllegalAccessException

			histogramMap.forEach((c, i) -> {
				builder.addRecord(TraceAbstractionProtos.TraceHistogram.Record.newBuilder().setCount(i)
						.setLetter(fromCodeblock(c)));
			});

		} catch (NoSuchFieldException | SecurityException | IllegalAccessException e) {
			e.printStackTrace();
			throw new IllegalStateException(e);
		}
		return builder.build();
	}

	private static TraceAbstractionProtos.IterationInfo fromIterationInfo(Info info) {
		TraceAbstractionProtos.IterationInfo.Builder builder;
		if (info.mBenchmark != null) {
			builder = fromCegarLoopStatisticsGenerator(info.mBenchmark);
		} else {
			builder = TraceAbstractionProtos.IterationInfo.newBuilder();
		}
		if (info.mAbstraction != null)
			builder.setAbstractionSizeInfo(info.mAbstraction);
		if (info.mInterpolantAutomaton != null)
			builder.setInterpolantAutomatonSizeInfo(info.mInterpolantAutomaton);
		if (info.mIteration != null)
			builder.setIteration(info.mIteration);
		return builder.build();
	}

	private static TraceAbstractionProtos.IterationInfo.Builder
			fromCegarLoopStatisticsGenerator(CegarLoopStatisticsGenerator benchmark) {
		final TraceAbstractionProtos.IterationInfo.Builder builder = TraceAbstractionProtos.IterationInfo.newBuilder();
		builder.setIteration((int) benchmark.getValue(CegarLoopStatisticsDefinitions.OverallIterations.toString()));
		final SizeIterationPair biggestAbstraction =
				(SizeIterationPair) benchmark.getValue(CegarLoopStatisticsDefinitions.BiggestAbstraction.toString());
		builder.setBiggestAbstraction(TraceAbstractionProtos.IterationInfo.Biggest.newBuilder()
				.setIteration(biggestAbstraction.getIteration()).setSize(biggestAbstraction.getSize()));
		return builder;
	}

	/*
	 * private static PredicateDoubleDecker.QueuePair fromQueuePair(PredicateQueuePair qPair) {
	 * PredicateDoubleDecker.QueuePair.Builder builder = PredicateDoubleDecker.QueuePair.newBuilder();
	 * qPair.mCallQueue.stream().map(TAConverter::fromDoubleDecker).forEach(builder::addCallQueue);
	 * qPair.mQueue.stream().map(TAConverter::fromDoubleDecker).forEach(builder::addQueue); return builder.build(); }
	 */

	private static PredicateDoubleDecker fromDoubleDecker(DoubleDecker<IPredicate> pdd) {
		final TraceAbstractionProtos.Predicate up = fromPredicate(pdd.getUp());
		final TraceAbstractionProtos.Predicate down = fromPredicate(pdd.getUp());
		return PredicateDoubleDecker.newBuilder().setUp(up).setDown(down).build();
	}

	/*
	 * private static PredicateQueueResult toDoubleDecker(PredicateDoubleDecker.QueueResponse response,
	 * PredicateQueuePair data) { final Deque<DoubleDecker<IPredicate>> queue; switch (response.getQueueType()) { case
	 * CALL: queue = data.mCallQueue; break; default: queue = data.mQueue; } final DoubleDecker<IPredicate>[] arr = new
	 * DoubleDecker[queue.size()]; DoubleDecker<IPredicate> result = queue.toArray(arr)[response.getIndex()]; assert
	 * queue.remove(result); return new PredicateQueueResult(result); }
	 */

	private static InteractiveIterationInfo fromIterationInfo(ParrotInteractiveIterationInfo itInfo) {
		return InteractiveIterationInfo.newBuilder().setNextInteractiveIteration(itInfo.getNextInteractiveIteration())
				.setFallback(convertTo(Strategy.class, itInfo.getFallbackStrategy())).build();
	}

	private static ParrotInteractiveIterationInfo toIterationInfo(InteractiveIterationInfo itInfo) {
		return new ParrotInteractiveIterationInfo(convertTo(RefinementStrategy.class, itInfo.getFallback()),
				itInfo.getNextInteractiveIteration());
	}

	private static TraceAbstractionProtos.Tracks
			fromTracks(MultiTrackTraceAbstractionRefinementStrategy.Track[] tracks) {
		final TraceAbstractionProtos.Tracks.Builder builder = TraceAbstractionProtos.Tracks.newBuilder();
		Arrays.stream(tracks).map(convertToEnum(TraceAbstractionProtos.Track.class)).forEach(builder::addTrack);
		return builder.build();
	}

	private static MultiTrackTraceAbstractionRefinementStrategy.Track[] toTracks(TraceAbstractionProtos.Tracks tracks) {
		return tracks.getTrackList().stream()
				.map(convertToEnum(MultiTrackTraceAbstractionRefinementStrategy.Track.class)).toArray(Track[]::new);
	}

	public static TraceAbstractionProtos.NestedRun fromNestedRun(NestedRun<CodeBlock, IPredicate> run) {
		TraceAbstractionProtos.NestedRun.Builder builder = TraceAbstractionProtos.NestedRun.newBuilder();
		run.getStateSequence().stream().map(TAConverter::fromPredicate).forEach(builder::addStateSequence);
		builder.setNestedword(fromNestedWord(run.getWord()));

		return builder.build();
	}

	public static TraceAbstractionProtos.NestedWord fromNestedWord(final NestedWord<CodeBlock> word) {
		final TraceAbstractionProtos.NestedWord.Builder builder = TraceAbstractionProtos.NestedWord.newBuilder();
		final TraceAbstractionProtos.NestingRelation.Builder nestingRelation =
				TraceAbstractionProtos.NestingRelation.newBuilder();

		for (int i = 0; i < word.length(); i++) {
			builder.addSymbol(fromCodeblock(word.getSymbol(i)));
			if (word.isCallPosition(i)) {
				if (word.isPendingCall(i))
					nestingRelation.addPendingCall(i);
				else
					nestingRelation.putInternalNesting(i, word.getReturnPosition(i));
			} else if (word.isReturnPosition(i)) {
				if (word.isPendingReturn(i))
					nestingRelation.addPendingReturn(i);
				else if (nestingRelation.getInternalNestingOrThrow(word.getCallPosition(i)) != i) {
					throw new IllegalArgumentException("Invalid Nested Run?");
					// builder.putInternalNesting(word.getCallPosition(i),i);
				}
			}
		}
		builder.setNestingRelation(nestingRelation);

		return builder.build();
	}

	/*
	 * public static NestedWord<CodeBlock> toNestedWord(TraceAbstractionProtos.NestedWord nestedWord) { CodeBlock[] word
	 * = new CodeBlock[] {}; int[] nestingrelation = new int[] {}; return new NestedWord<>(word, nestingrelation); }
	 *
	 * 
	 * public static NestedRun<CodeBlock, IPredicate> toNestedRun(TraceAbstractionProtos.NestedRun run) {
	 * NestedWord<CodeBlock> nestedWord = new NestedWord<>(); ArrayList<IPredicate> stateSequence = new ArrayList<>();
	 * // run.getst return new NestedRun<>(nestedWord, stateSequence); }
	 */

	public static TraceAbstractionProtos.NestedWordAutomaton
			fromAutomaton(INestedWordAutomaton<CodeBlock, IPredicate> automaton) {
		final TraceAbstractionProtos.NestedWordAutomaton.Builder builder =
				TraceAbstractionProtos.NestedWordAutomaton.newBuilder();
		final List<CodeBlock> callAlphabet = new ArrayList<>();
		final List<CodeBlock> internalAlphabet = new ArrayList<>();
		final List<CodeBlock> returnAlphabet = new ArrayList<>();
		copyAlphabets(automaton, callAlphabet, internalAlphabet, returnAlphabet, builder);

		final List<IPredicate> states = new ArrayList<>();

		automaton.getStates().forEach(states::add);
		final Function<IPredicate, Consumer<Consumer<Integer>>> addStateRef = addRef(states);

		addStateRef.apply(automaton.getEmptyStackState()).accept(builder::setEmptyStack);

		for (IPredicate state : states) {
			Consumer<Consumer<Integer>> addStateStateRef = addStateRef.apply(state);
			builder.addStates(fromPredicate(state));
			if (automaton.isInitial(state))
				addStateStateRef.accept(builder::addInitial);
			if (automaton.isFinal(state))
				addStateStateRef.accept(builder::addFinal);

			stream(automaton.internalSuccessors(state)).map(getTransition(addStateStateRef, internalAlphabet, states))
					.forEach(builder::addInternalEdges);
			stream(automaton.callSuccessors(state)).map(getTransition(addStateStateRef, callAlphabet, states))
					.forEach(builder::addCallEdges);
			stream(automaton.returnSuccessors(state)).map(getTransition(addStateStateRef, returnAlphabet, states))
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

	private static void copyAlphabets(INestedWordAutomatonSimple<CodeBlock, IPredicate> fromNwa,
			List<CodeBlock> callAlphabet, List<CodeBlock> internalAlphabet, List<CodeBlock> returnAlphabet,
			TraceAbstractionProtos.NestedWordAutomaton.Builder toNwa) {
		fromNwa.getCallAlphabet().forEach(callAlphabet::add);
		fromNwa.getInternalAlphabet().forEach(internalAlphabet::add);
		fromNwa.getReturnAlphabet().forEach(returnAlphabet::add);
		toNwa.setCall(fromAlphabet(callAlphabet)).setInternal(fromAlphabet(internalAlphabet))
				.setReturn(fromAlphabet(returnAlphabet));
	}

	public static TraceAbstractionProtos.NestedWordAutomaton
			fromSimpleAutomaton(INestedWordAutomatonSimple<CodeBlock, IPredicate> automaton) {
		final TraceAbstractionProtos.NestedWordAutomaton.Builder builder =
				TraceAbstractionProtos.NestedWordAutomaton.newBuilder();
		final List<CodeBlock> callAlphabet = new ArrayList<>();
		final List<CodeBlock> internalAlphabet = new ArrayList<>();
		final List<CodeBlock> returnAlphabet = new ArrayList<>();
		copyAlphabets(automaton, callAlphabet, internalAlphabet, returnAlphabet, builder);

		final Set<IPredicate> callStates = new HashSet<>();
		final List<IPredicate> states = new ArrayList<>();
		final Set<IPredicate> visitedStates = new HashSet<>();
		final Deque<IPredicate> openStates = new ArrayDeque<>();

		automaton.getInitialStates().forEach(openStates::add);

		final Function<IPredicate, Consumer<Consumer<Integer>>> addStateRef = addRef(states);
		addStateRef.apply(automaton.getEmptyStackState()).accept(builder::setEmptyStack);

		while (!openStates.isEmpty()) {
			IPredicate state = openStates.removeFirst();
			if (!visitedStates.add(state))
				continue;
			states.add(state);

			automaton.callSuccessors(state).forEach(t -> {
				callStates.add(state);
				openStates.add(t.getSucc());
			});
			automaton.internalSuccessors(state).forEach(t -> openStates.add(t.getSucc()));
			callStates.forEach(
					hier -> automaton.returnSuccessorsGivenHier(state, hier).forEach(t -> openStates.add(t.getSucc())));
		}

		for (IPredicate state : states) {
			Consumer<Consumer<Integer>> addStateStateRef = addStateRef.apply(state);
			builder.addStates(fromPredicate(state));
			if (automaton.isInitial(state))
				addStateStateRef.accept(builder::addInitial);
			if (automaton.isFinal(state))
				addStateStateRef.accept(builder::addFinal);

			stream(automaton.internalSuccessors(state)).map(getTransition(addStateStateRef, internalAlphabet, states))
					.forEach(builder::addInternalEdges);
			stream(automaton.callSuccessors(state)).map(getTransition(addStateStateRef, callAlphabet, states))
					.forEach(builder::addCallEdges);
			callStates.forEach(hier -> stream(automaton.returnSuccessorsGivenHier(state, hier))
					.map(getTransition(addStateStateRef, returnAlphabet, states)).forEach(builder::addReturnEdges));
		}

		return builder.build();
	}

	private static <T> Stream<T> stream(Iterable<T> source) {
		return StreamSupport.stream(source.spliterator(), false);
	}

	private static
			Function<IOutgoingTransitionlet<CodeBlock, IPredicate>, TraceAbstractionProtos.NestedWordAutomaton.transition.Builder>
			getTransition(final Consumer<Consumer<Integer>> origin, List<CodeBlock> alphabet, List<IPredicate> states) {
		return transition -> {
			final TraceAbstractionProtos.NestedWordAutomaton.transition.Builder builder =
					TraceAbstractionProtos.NestedWordAutomaton.transition.newBuilder();
			origin.accept(builder::setOriginState);
			addRef(states).apply(transition.getSucc()).accept(builder::setSuccessorState);
			addRef(alphabet).apply(transition.getLetter()).accept(builder::setLetter);
			return builder;
		};
	}

	/**
	 * Creates Integer References to positions of List elements
	 * 
	 * @param targets
	 *            elements that should be referenced
	 * @return a Function that should be passed the target element which should be referenced to the result. The
	 *         resulting accepts a setter which expects the integer reference. This setter might be a reference to a
	 *         setter function from protobuf.
	 */
	private static <T> Function<T, Consumer<Consumer<Integer>>> addRef(final List<T> targets) {
		return t -> {
			int i = targets.indexOf(t);
			return consumer -> consumer.accept(i);
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
		final TraceAbstractionProtos.NestedWordAutomaton.transition.Builder builder =
				TraceAbstractionProtos.NestedWordAutomaton.transition.newBuilder();
		for (Map.Entry<IPredicate, Map<CodeBlock, Set<IPredicate>>> transition : transitions.entrySet()) {
			final int firstIndex = states.indexOf(transition.getKey());
		}
		return builder.build();
	}

	public static TraceAbstractionProtos.CodeBlock fromCodeblock(CodeBlock codeblock) {
		return TraceAbstractionProtos.CodeBlock.newBuilder().setSerial(codeblock.getSerialNumber())
				.setCode(codeblock.getPrettyPrintedStatements()).build();
	}

	public static TraceAbstractionProtos.IcfgLocation fromLocation(IcfgLocation location) {
		return TraceAbstractionProtos.IcfgLocation.newBuilder().setDebugIdentifier(location.getDebugIdentifier())
				.setProcedure(location.getProcedure()).build();
	}

	public static TraceAbstractionProtos.Predicate fromPredicate(IPredicate predicate) {
		final TraceAbstractionProtos.Predicate.Builder builder = TraceAbstractionProtos.Predicate.newBuilder();
		if (predicate instanceof ISLPredicate) {
			ISLPredicate islPred = (ISLPredicate) predicate;
			builder.addLocation(fromLocation(islPred.getProgramPoint()));
		} else if (predicate instanceof IMLPredicate) {
			IMLPredicate imlPred = (IMLPredicate) predicate;
			Arrays.stream(imlPred.getProgramPoints()).map(TAConverter::fromLocation).forEach(builder::addLocation);
		}
		builder.setFormulaString(predicate.getFormula().toString());
		try {
			builder.setFormulaHashCode(predicate.getFormula().hashCode());
			Arrays.stream(predicate.getProcedures()).forEach(builder::addProcedures);
		} catch (UnsupportedOperationException e) {
		}
		return builder.build();
	}

	public static TraceAbstractionProtos.TAPreferences fromTAPreferences(TAPreferences preferences) {
		final InterpolantAutomatonEnhancement enhancment;
		switch (preferences.interpolantAutomatonEnhancement()) {
		case NONE:
			enhancment = InterpolantAutomatonEnhancement.NO_ENHANCEMENT;
			break;
		default:
			enhancment =
					convertTo(InterpolantAutomatonEnhancement.class, preferences.interpolantAutomatonEnhancement());
		}

		final Minimization minimization;
		switch (preferences.getMinimization()) {
		case NONE:
			minimization = Minimization.NO_MINIMIZATION;
			break;

		default:
			minimization = convertTo(Minimization.class, preferences.getMinimization());
			break;
		}

		return TraceAbstractionProtos.TAPreferences.newBuilder().setMInterprocedural(preferences.interprocedural())
				.setMMaxIterations(preferences.maxIterations()).setMWatchIteration(preferences.watchIteration())
				.setMArtifact(convertTo(Artifact.class, preferences.artifact()))
				.setMInterpolation(convertTo(InterpolationTechnique.class, preferences.interpolation()))
				.setMInterpolantAutomaton(convertTo(InterpolantAutomaton.class, preferences.interpolantAutomaton()))
				.setMDumpAutomata(preferences.dumpAutomata())
				.setMAutomataFormat(convertTo(Format.class, preferences.getAutomataFormat()))
				.setMDumpPath(preferences.dumpPath()).setMDeterminiation(enhancment).setMMinimize(minimization)
				.setMHoare(preferences.computeHoareAnnotation())
				.setMConcurrency(convertTo(Concurrency.class, preferences.getConcurrency()))
				.setMHoareTripleChecks(convertTo(HoareTripleChecks.class, preferences.getHoareTripleChecks()))
				.setMHoareAnnotationPositions(
						convertTo(HoareAnnotationPositions.class, preferences.getHoareAnnotationPositions()))
				.build();
	}

	public static TraceAbstractionProtos.CegarResult fromResult(AbstractCegarLoop.Result result) {
		return TraceAbstractionProtos.CegarResult.newBuilder().setResult(convertTo(Result.class, result)).build();
	}

	public static <E extends Enum<E>> Function<Enum<?>, E> convertToEnum(Class<E> toCls) {
		return f -> convertTo(toCls, f);
	}

	public static <E extends Enum<E>> E convertTo(Class<E> toCls, Enum<?> from) {
		return Enum.valueOf(toCls, from.name());
	}
}