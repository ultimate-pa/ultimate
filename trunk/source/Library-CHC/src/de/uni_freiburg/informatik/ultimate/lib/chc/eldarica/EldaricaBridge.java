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

import ap.SimpleAPI;
import ap.parser.IAtom;
import ap.parser.IFormula;
import ap.terfor.preds.Predicate;
import de.uni_freiburg.informatik.ultimate.lib.chc.Derivation;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.chc.IChcScript;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.Lazy;
import lazabs.horn.bottomup.HornClauses.Clause;
import lazabs.horn.bottomup.SimpleWrapper;
import lazabs.prover.Tree;
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
public class EldaricaBridge implements IChcScript, AutoCloseable {
	private final Script mScript;
	private final SimpleAPI mPrincess;

	private boolean mProduceModels = false;
	private boolean mProduceDerivations = false;
	private boolean mProduceUnsatCores = false;

	private Translator mTranslator;
	private Map<Clause, HornClause> mClauseMap;

	private LBool mLastResult = null;
	private Lazy<Map<HcPredicateSymbol, Term>> mLastModel;
	private Lazy<Derivation> mLastDerivation;
	private Lazy<Set<HornClause>> mLastUnsatCore;

	@Deprecated
	public static void doStuff(final Script script, final HcSymbolTable symbolTable,
			final java.util.List<HornClause> clauses) {
		new EldaricaBridge(script).solve(symbolTable, clauses);
	}

	public EldaricaBridge(final Script script) {
		// TODO allow setting a timeout (see eldarica's GlobalParameters object)
		mScript = script;
		mPrincess = SimpleAPI.apply(SimpleAPI.apply$default$1(), SimpleAPI.apply$default$2(),
				SimpleAPI.apply$default$3(), SimpleAPI.apply$default$4(), SimpleAPI.apply$default$5(),
				SimpleAPI.apply$default$6(), SimpleAPI.apply$default$7(), SimpleAPI.apply$default$8(),
				SimpleAPI.apply$default$9(), SimpleAPI.apply$default$10());
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

	@Override
	public Script getScript() {
		return mScript;
	}

	@Override
	public LBool solve(final HcSymbolTable symbolTable, final java.util.List<HornClause> system) {
		reset();

		final var translatedClauses = translateSystem(system);
		final var result = SimpleWrapper.solveLazily(translatedClauses, SimpleWrapper.solve$default$2(),
				SimpleWrapper.solve$default$3(), SimpleWrapper.solve$default$4(), SimpleWrapper.solve$default$6());

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
					mLastDerivation = new Lazy<>(
							() -> translateDerivation(backtranslator, clauseMap, derivationBuilder.apply().toTree()));
				}
				if (mProduceUnsatCores) {
					mLastUnsatCore = new Lazy<>(() -> extractUnsatCore(clauseMap, derivationBuilder.apply().toTree()));
				}
			}
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
		// TODO from map to model -- see other branch
		mLastModel.get();
		return null;
	}

	private static Map<HcPredicateSymbol, Term> translateModel(final Backtranslator backtranslator,
			final scala.collection.Map<Predicate, IFormula> model) {
		final var translatedModel = new HashMap<HcPredicateSymbol, Term>();
		for (final var entry : ofMap(model).entrySet()) {
			final var pred = backtranslator.translatePredicate(entry.getKey());
			final var body = backtranslator.translateFormula(entry.getValue());
			translatedModel.put(pred, body);
		}
		return translatedModel;
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
			final var term = backtranslator.translateTerm(arg, sort);
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
}
