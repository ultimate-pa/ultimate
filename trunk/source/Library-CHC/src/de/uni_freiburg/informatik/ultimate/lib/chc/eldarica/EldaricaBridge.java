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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Collectors;

import ap.SimpleAPI;
import ap.parser.IAtom;
import ap.parser.IFormula;
import ap.terfor.preds.Predicate;
import de.uni_freiburg.informatik.ultimate.lib.chc.Derivation;
import de.uni_freiburg.informatik.ultimate.lib.chc.HcPredicateSymbol;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import lazabs.horn.bottomup.HornClauses.Clause;
import lazabs.horn.bottomup.SimpleWrapper;
import lazabs.prover.Tree;
import scala.Tuple2;
import scala.collection.JavaConverters;
import scala.collection.Seq;
import scala.collection.immutable.List;
import scala.runtime.AbstractFunction1;

public class EldaricaBridge {
	private final Translator mTranslator;
	private final Map<Clause, HornClause> mClauseMap = new HashMap<>();

	public static void doStuff(final Script script, final java.util.Collection<HornClause> clauses) {
		SimpleAPI.<Object> withProver(new AbstractFunction1<>() {
			@Override
			public Object apply(final SimpleAPI princess) {
				return new EldaricaBridge(script, princess, clauses);
			}
		});
	}

	public EldaricaBridge(final Script script, final SimpleAPI princess,
			final java.util.Collection<HornClause> clauses) {
		mTranslator = new Translator(princess);

		final var translatedClauses = translateSystem(clauses);
		final var result = SimpleWrapper.solve(translatedClauses, SimpleWrapper.solve$default$2(),
				SimpleWrapper.solve$default$3(), SimpleWrapper.solve$default$4(), SimpleWrapper.solve$default$5(),
				SimpleWrapper.solve$default$6());

		final var backtranslator = mTranslator.createBacktranslator(script);

		if (result.isLeft()) {
			System.out.println("SAT");
			final var solution = translateModel(backtranslator, result.left().get());
		} else {
			System.out.println("UNSAT");
			final var derivation = translateDerivation(backtranslator, result.right().get().toTree());
		}
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

	private Derivation translateDerivation(final Backtranslator backtranslator,
			final Tree<Tuple2<IAtom, Clause>> tree) {
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

		final var children = ofList(tree.children()).stream().map(c -> translateDerivation(backtranslator, c))
				.collect(Collectors.toList());
		return new Derivation(pred, args, mClauseMap.get(tree.d()._2()), children);
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
}
