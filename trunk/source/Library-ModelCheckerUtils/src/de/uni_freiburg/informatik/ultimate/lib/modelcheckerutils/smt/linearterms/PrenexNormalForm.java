/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ContainsQuantifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.NonCoreBooleanSubTermTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Transform a Term into prenex normal form (quantifiers outside).
 *
 * @author Matthias Heizmann
 *
 */
public class PrenexNormalForm extends TermTransformer {

	private final Script mScript;
	private final ManagedScript mMgdScript;

	public PrenexNormalForm(final ManagedScript mgdScript) {
		mScript = mgdScript.getScript();
		mMgdScript = mgdScript;
	}



	@Override
	protected void convert(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final String fun = appTerm.getFunction().getName();
			if (fun.equals("ite")) {
				if (new ContainsQuantifier().containsQuantifier(appTerm)) {
					throw new UnsupportedOperationException("ite Term with quantifier, use IteRemover first");
				} else {
					// since the subTerm does not contain quantifier we can immediately use this as a result
					setResult(appTerm);
					return;
				}
			}
		}
		super.convert(term);
	}



	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		if (NonCoreBooleanSubTermTransformer.isCoreBoolean(appTerm)) {
			final String fun = appTerm.getFunction().getName();
			if (fun.equals("=")) {
				throw new UnsupportedOperationException("not yet implemented, we need term in nnf");
			} else if (fun.equals("not")) {
				final Term result = pullQuantifiersNot(newArgs);
				setResult(result);
			} else if (fun.equals("and")) {
				final Term result = pullQuantifiers(appTerm, newArgs);
				setResult(result);
			} else if (fun.equals("or")) {
				final Term result = pullQuantifiers(appTerm, newArgs);
				setResult(result);
			} else if (fun.equals("=>")) {
				throw new UnsupportedOperationException("not yet implemented, we need term in nnf");
			} else if (fun.equals("xor")) {
				throw new UnsupportedOperationException("not yet implemented, we need term in nnf");
			} else if (fun.equals("distinct")) {
				throw new UnsupportedOperationException("not yet implemented, we need term in nnf");
			} else if (fun.equals("ite")) {
				throw new UnsupportedOperationException("not yet implemented, we need term in nnf");
			} else {
				throw new AssertionError("unknown core boolean term");
			}
		} else {
			super.convertApplicationTerm(appTerm, newArgs);
		}
	}

	private Term pullQuantifiersNot(final Term[] newArgs) {
		assert newArgs.length == 1 : "no not";
		final Term notArg = newArgs[0];
		final QuantifierSequence quantifierSequence = new QuantifierSequence(mScript, notArg);
		final Term inner = quantifierSequence.getInnerTerm();
		final List<QuantifierSequence.QuantifiedVariables> qVarSeq = quantifierSequence.getQuantifierBlocks();
		Term result = SmtUtils.not(mScript, inner);
		for (int i = qVarSeq.size()-1; i>=0; i--) {
			final QuantifierSequence.QuantifiedVariables quantifiedVars = qVarSeq.get(i);
			final int resultQuantifier = (quantifiedVars.getQuantifier() + 1) % 2;
			result = SmtUtils.quantifier(mScript, resultQuantifier,
					quantifiedVars.getVariables(), result);
		}
		return result;
	}

	private Term pullQuantifiers(final ApplicationTerm appTerm, final Term[] newArgs) {
		final QuantifierSequence[] quantifierSequences = new QuantifierSequence[newArgs.length];
		final HashSet<TermVariable> freeVariables = new HashSet<>();
		for (int i=0; i<newArgs.length; i++) {
			freeVariables.addAll(Arrays.asList(newArgs[i].getFreeVars()));
			quantifierSequences[i] = new QuantifierSequence(mScript, newArgs[i]);
		}
		final Term result = QuantifierSequence.mergeQuantifierSequences(mMgdScript,
				appTerm.getFunction().getName(), quantifierSequences,
				freeVariables);
		return result;
	}

	@Override
	public void postConvertLet(final LetTerm oldLet, final Term[] newValues, final Term newBody) {
		throw new UnsupportedOperationException("not yet implemented, we need term without let");
	}



	@Override
	public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
		if (SmtUtils.isQuantifiedFormulaWithSameQuantifier(old.getQuantifier(), newBody) != null) {
			final Term result = SmtUtils.quantifier(mScript, old.getQuantifier(),
					new HashSet<TermVariable>(Arrays.asList(old.getVariables())), newBody);
			setResult(result);
		} else {
			super.postConvertQuantifier(old, newBody);
		}
	}

	@Override
	public void postConvertAnnotation(final AnnotatedTerm old, final Annotation[] newAnnots, final Term newBody) {
		setResult(newBody);
//		Term result = mScript.annotate(newBody, newAnnots);
//		setResult(result);
//		throw new UnsupportedOperationException("not yet implemented: annotations");
	}
}
