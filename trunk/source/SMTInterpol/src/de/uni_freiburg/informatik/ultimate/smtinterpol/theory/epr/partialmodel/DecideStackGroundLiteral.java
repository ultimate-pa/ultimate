/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel;

import java.util.ArrayList;
import java.util.List;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms.EprGroundPredicateAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;

/**
 * Represents an entry in the epr decide stack which marks the setting of a literal through the dpll engine at that
 * point.
 *
 * @author Alexander Nutz, Jochen Hoenicke
 */
public class DecideStackGroundLiteral extends DecideStackEntry {

	private final Literal mLiteral;
	private boolean isEffective;

	public DecideStackGroundLiteral(final Literal l) {
		mLiteral = l;
	}

	@Override
	public String toString() {
		return "(literal: " + mLiteral + ")";
	}

	public Literal getLiteral() {
		return mLiteral;
	}

	public EprPredicate getEprPredicate() {
		if (mLiteral.getAtom() instanceof EprGroundPredicateAtom) {
			final EprGroundPredicateAtom eprAtom = (EprGroundPredicateAtom) mLiteral.getAtom();
			return eprAtom.getEprPredicate();
		}
		return null;
	}

	@Override
	public DawgState<ApplicationTerm, EprTheory.TriBool> getDawg() {
		if (mLiteral.getAtom() instanceof EprGroundPredicateAtom) {
			final EprGroundPredicateAtom eprAtom = (EprGroundPredicateAtom) mLiteral.getAtom();
			final EprPredicate eprPred = eprAtom.mEprPredicate;
			final List<ApplicationTerm> word = new ArrayList<>();
			for (final Term param : eprAtom.getArguments()) {
				word.add((ApplicationTerm) param);
			}
			final DawgFactory<ApplicationTerm, TermVariable> factory = eprPred.getEprTheory()
					.getDawgFactory();
			return factory.createMapped(factory.createSingletonSet(eprPred.getSignature(), word),
					b -> b ? (mLiteral == eprAtom ? EprTheory.TriBool.TRUE : EprTheory.TriBool.FALSE)
							: EprTheory.TriBool.UNKNOWN);
		}
		return null;
	}

	@Override
	public void push(EprDecideStack stack) {
		if (mLiteral.getAtom() instanceof EprGroundPredicateAtom) {
			final EprGroundPredicateAtom eprAtom = (EprGroundPredicateAtom) mLiteral.getAtom();
			final DawgState<ApplicationTerm, EprTheory.TriBool> dawg = eprAtom.mEprPredicate.getDawg();
			final List<ApplicationTerm> word = new ArrayList<>();
			for (final Term param : eprAtom.getArguments()) {
				word.add((ApplicationTerm) param);
			}
			if (dawg.getValue(word) == EprTheory.TriBool.UNKNOWN) {
				final BiFunction<EprTheory.TriBool, Boolean, EprTheory.TriBool> combinator = (old, setLit) -> {
					assert !setLit || old == EprTheory.TriBool.UNKNOWN;
					return (setLit ? (mLiteral == eprAtom ? EprTheory.TriBool.TRUE : EprTheory.TriBool.FALSE) : old);
				};
				isEffective = true;
				final DawgFactory<ApplicationTerm, TermVariable> factory =
						eprAtom.mEprPredicate.getEprTheory().getDawgFactory();
				eprAtom.mEprPredicate.setDawg(factory.createProduct(dawg,
						factory.createSingletonSet(eprAtom.mEprPredicate.getSignature(), word), combinator));
			}
		}
	}

	@Override
	public void pop(EprDecideStack stack) {
		if (isEffective) {
			final EprGroundPredicateAtom eprAtom = (EprGroundPredicateAtom) mLiteral.getAtom();
			final DawgState<ApplicationTerm, EprTheory.TriBool> dawg = eprAtom.mEprPredicate.getDawg();
			final List<ApplicationTerm> word = new ArrayList<>();
			for (final Term param : eprAtom.getArguments()) {
				word.add((ApplicationTerm) param);
			}
			final BiFunction<EprTheory.TriBool, Boolean, EprTheory.TriBool> combinator = (old, setLit) -> {
				return (setLit ? EprTheory.TriBool.UNKNOWN : old);
			};
			isEffective = false;
			final DawgFactory<ApplicationTerm, TermVariable> factory =
					eprAtom.mEprPredicate.getEprTheory().getDawgFactory();
			eprAtom.mEprPredicate.setDawg(factory.createProduct(dawg,
					factory.createSingletonSet(eprAtom.mEprPredicate.getSignature(), word), combinator));
		}
	}
}
