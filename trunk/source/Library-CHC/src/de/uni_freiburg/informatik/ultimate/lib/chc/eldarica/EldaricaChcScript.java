/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE CHC Library.
 *
 * The ULTIMATE CHC Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CHC Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CHC Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CHC Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CHC Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.chc.eldarica;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import ap.SimpleAPI;
import ap.parser.IAtom;
import ap.parser.IFormula;
import ap.terfor.preds.Predicate;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.chc.Derivation;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.IChcScript;
import de.uni_freiburg.informatik.ultimate.lib.chc.eldarica.Backtranslator.IBoundVariableContext;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.FunctionDefinition;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.ModelDescription;
import de.uni_freiburg.informatik.ultimate.util.Lazy;
import lazabs.GlobalParameters;
import lazabs.horn.bottomup.HornClauses.Clause;
import lazabs.horn.bottomup.SimpleWrapper;
import lazabs.prover.Tree;
import scala.Option;
import scala.Tuple2;
import scala.collection.JavaConverters;
import scala.collection.Seq;
import scala.collection.immutable.List;

/**
 * Provides access to the eldarica constraint Horn solver.
 *
 * https://github.com/uuverifiers/eldarica/
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class EldaricaChcScript implements IChcScript, AutoCloseable {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final Script mScript;
	private final SimpleAPI mPrincess;

	private final long mDefaultQueryTimeout;
	private boolean mProduceModels = false;
	private boolean mProduceDerivations = false;
	private boolean mProduceUnsatCores = false;

	private Translator mTranslator;
	private Map<Clause, HornClause> mClauseMap;

	private LBool mLastResult = null;
	private Lazy<ModelDescription> mLastModel;
	private Lazy<Derivation> mLastDerivation;
	private Lazy<Set<HornClause>> mLastUnsatCore;

	public EldaricaChcScript(final IUltimateServiceProvider services, final Script script) {
		this(services, script, -1L);
	}

	public EldaricaChcScript(final IUltimateServiceProvider services, final Script script,
			final long defaultQueryTimeout) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		mScript = script;
		mPrincess = SimpleAPI.apply(SimpleAPI.apply$default$1(), SimpleAPI.apply$default$2(),
				SimpleAPI.apply$default$3(), SimpleAPI.apply$default$4(), SimpleAPI.apply$default$5(),
				SimpleAPI.apply$default$6(), SimpleAPI.apply$default$7(), SimpleAPI.apply$default$8(),
				SimpleAPI.apply$default$9(), SimpleAPI.apply$default$10());
		mDefaultQueryTimeout = defaultQueryTimeout;
	}

	@Override
	public Script getScript() {
		return mScript;
	}

	@Override
	public LBool solve(final HcSymbolTable symbolTable, final java.util.List<HornClause> system) {
		return solve(symbolTable, system, -1L);
	}

	@Override
	public LBool solve(final HcSymbolTable symbolTable, final java.util.List<HornClause> system, final long timeout) {
		reset();
		setupTimeout(timeout);

		final var translatedClauses = translateSystem(system);
		try {
			if (0 == 1) {
				// Unreachable dummy code so Java doesn't think the catch block is unreachable.
				// Necessary because the scala API does not declare checked exceptions.
				throw new lazabs.Main.TimeoutException$();
			}

			mLogger.info("starting eldarica solver...");
			final var result = SimpleWrapper.solveLazily(translatedClauses, SimpleWrapper.solve$default$2(),
					SimpleWrapper.solve$default$3(), SimpleWrapper.solve$default$4(), SimpleWrapper.solve$default$6());
			mLogger.info("eldarica has returned successfully.");

			final var backtranslator = mTranslator.createBacktranslator(mScript);

			if (result.isLeft()) {
				mLastResult = LBool.SAT;
				if (mProduceModels) {
					final var modelBuilder = result.left().get();
					mLastModel = new Lazy<>(() -> translateModel(backtranslator, modelBuilder.apply()));
				}
			} else {
				mLastResult = LBool.UNSAT;
				if (mProduceDerivations || mProduceUnsatCores) {
					final var derivationBuilder = result.right().get();
					final var clauseMap = mClauseMap;
					if (mProduceDerivations) {
						mLastDerivation = new Lazy<>(() -> translateDerivation(backtranslator, clauseMap,
								derivationBuilder.apply().toTree()));
					}
					if (mProduceUnsatCores) {
						mLastUnsatCore =
								new Lazy<>(() -> extractUnsatCore(clauseMap, derivationBuilder.apply().toTree()));
					}
				}
			}
		} catch (final lazabs.Main.TimeoutException$ e) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(getClass(), "solving CHC system");
			}
			mLogger.warn("Eldarica timed out, returning UNKNOWN: %s", e);
			mLastResult = LBool.UNKNOWN;
		}
		return mLastResult;
	}

	private List<Clause> translateSystem(final java.util.Collection<HornClause> system) {
		final var translatedClauses = new ArrayList<Clause>(system.size());
		for (final var clause : system) {
			final var translated = mTranslator.translateClause(clause);
			mClauseMap.put(translated, clause);
			translatedClauses.add(translated);
		}
		return toList(translatedClauses);
	}

	@Override
	public boolean supportsModelProduction() {
		return true;
	}

	@Override
	public void produceModels(final boolean enable) {
		mProduceModels = enable;
	}

	@Override
	public Optional<Model> getModel() {
		if (mLastResult != LBool.SAT) {
			throw new UnsupportedOperationException("No model available: last query was " + mLastResult);
		}
		if (mLastModel == null) {
			return Optional.empty();
		}
		return Optional.of(mLastModel.get());
	}

	private ModelDescription translateModel(final Backtranslator backtranslator,
			final scala.collection.Map<Predicate, IFormula> model) {
		final var translatedDefs = new HashSet<FunctionDefinition>();
		for (final var entry : ofMap(model).entrySet()) {
			final var pred = backtranslator.translatePredicate(entry.getKey());
			final var ctx = new PredicateContext(mScript, pred);
			final var body = backtranslator.translateFormula(entry.getValue(), ctx);
			translatedDefs.add(new FunctionDefinition(pred.getFunctionSymbol(), ctx.getParameters(), body));
		}
		return new ModelDescription(translatedDefs);
	}

	@Override
	public boolean supportsDerivationProduction() {
		return true;
	}

	@Override
	public void produceDerivations(final boolean enable) {
		mProduceDerivations = enable;
	}

	@Override
	public Optional<Derivation> getDerivation() {
		if (mLastResult != LBool.UNSAT) {
			throw new UnsupportedOperationException("No derivation available: last query was " + mLastResult);
		}
		if (mLastDerivation == null) {
			return Optional.empty();
		}
		return Optional.of(mLastDerivation.get());
	}

	private static Derivation translateDerivation(final Backtranslator backtranslator,
			final Map<Clause, HornClause> clauseMap, final Tree<Tuple2<IAtom, Clause>> tree) {
		final var atom = tree.d()._1();
		final var pred = backtranslator.translatePredicate(atom.pred());

		final var args = new ArrayList<Term>(atom.args().length());
		int i = 0;
		for (final var arg : ofList(atom.args())) {
			final var sort = pred.getParameterSorts().get(i);
			final var term = backtranslator.translateTerm(arg, sort, null);
			args.add(term);
			i++;
		}

		final var children = ofList(tree.children()).stream()
				.map(c -> translateDerivation(backtranslator, clauseMap, c)).collect(Collectors.toList());
		return new Derivation(pred, args, clauseMap.get(tree.d()._2()), children);
	}

	@Override
	public boolean supportsUnsatCores() {
		return true;
	}

	@Override
	public void produceUnsatCores(final boolean enable) {
		mProduceUnsatCores = enable;
	}

	@Override
	public Optional<Set<HornClause>> getUnsatCore() {
		if (mLastResult != LBool.UNSAT) {
			throw new UnsupportedOperationException("No UNSAT core available: last query was " + mLastResult);
		}
		if (mLastUnsatCore == null) {
			return Optional.empty();
		}
		return Optional.of(mLastUnsatCore.get());
	}

	private static Set<HornClause> extractUnsatCore(final Map<Clause, HornClause> clauseMap,
			final Tree<Tuple2<IAtom, Clause>> derivation) {
		final var worklist = new ArrayDeque<Tree<Tuple2<IAtom, Clause>>>();
		worklist.add(derivation);

		final var result = new HashSet<HornClause>();
		while (!worklist.isEmpty()) {
			final var tree = worklist.pop();
			final var clause = tree.d()._2();
			result.add(clauseMap.get(clause));
			worklist.addAll(ofList(tree.children()));
		}
		return result;
	}

	private void reset() {
		mClauseMap = new HashMap<>();
		mTranslator = new Translator(mPrincess);

		mLastModel = null;
		mLastDerivation = null;
		mLastUnsatCore = null;
	}

	@Override
	public void close() throws Exception {
		mPrincess.shutDown();
	}

	private void setupTimeout(final long queryTimeout) {
		// set the timeout parameter itself
		final var actualTimeout = determineTimeout(queryTimeout);
		mLogger.info("setting eldarica timeout (in ms) to %s", actualTimeout);
		GlobalParameters.get().timeout_$eq((Option) actualTimeout);

		// we need to override the timeout checking logic, because eldarica only does this in its main() method
		final var pms = mServices.getProgressMonitorService();
		final long startTime = System.currentTimeMillis();
		GlobalParameters.get().timeoutChecker_$eq(new scala.runtime.AbstractFunction0<>() {
			@Override
			public scala.runtime.BoxedUnit apply() {
				if (!pms.continueProcessing() || (actualTimeout.isDefined()
						&& System.currentTimeMillis() - startTime > actualTimeout.get())) {
					// Nasty hack to trick java into throwing TimeoutException, a checked exception.
					// (This is necessary, because scala does not declare checked exceptions.)
					throwUnchecked(new lazabs.Main.TimeoutException$());
				}
				return scala.runtime.BoxedUnit.UNIT;
			}
		});
	}

	private Option<Integer> determineTimeout(final long queryTimeout) {
		final var globalTimeout = mServices.getProgressMonitorService().remainingTime();
		final var currentTimeout = queryTimeout <= 0 ? mDefaultQueryTimeout : queryTimeout;
		final var actualTimeout = currentTimeout <= 0 ? globalTimeout : Long.min(currentTimeout, globalTimeout);
		return actualTimeout < 0 ? Option.empty() : Option.apply((int) actualTimeout);
	}

	private static <T extends Throwable> void throwUnchecked(final Throwable e) throws T {
		throw (T) e;
	}

	private static <X> List<X> toList(final java.util.List<X> list) {
		return JavaConverters.asScalaIteratorConverter(list.iterator()).asScala().toList();
	}

	private static <X> java.util.List<X> ofList(final Seq<X> list) {
		return JavaConverters.seqAsJavaListConverter(list).asJava();
	}

	private static <K, V> Map<K, V> ofMap(final scala.collection.Map<K, V> map) {
		return JavaConverters.mapAsJavaMapConverter(map).asJava();
	}

	private static class PredicateContext implements IBoundVariableContext {
		private final Script mScript;
		private final HcPredicateSymbol mPredicate;

		public PredicateContext(final Script script, final HcPredicateSymbol predicate) {
			mScript = script;
			mPredicate = predicate;
		}

		@Override
		public TermVariable getBoundVariable(final int index) {
			final var sort = mPredicate.getParameterSorts().get(index);
			return mScript.variable("~~" + mPredicate.getFunctionSymbol() + "~" + index, sort);
		}

		public TermVariable[] getParameters() {
			return IntStream.range(0, mPredicate.getArity()).mapToObj(this::getBoundVariable)
					.toArray(TermVariable[]::new);
		}
	}
}
