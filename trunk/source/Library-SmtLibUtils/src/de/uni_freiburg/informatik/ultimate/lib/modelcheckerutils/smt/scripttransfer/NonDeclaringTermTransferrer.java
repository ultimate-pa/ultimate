/*
 * Copyright (C) 2015-2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class NonDeclaringTermTransferrer extends TermTransformer {

	private final boolean mApplyLocalSimplifications;
	private final Script mScript;

	public NonDeclaringTermTransferrer(final Script script) {
		this(script, false);
	}

	public NonDeclaringTermTransferrer(final Script script, final boolean applyLocalSimplifications) {
		mScript = script;
		mApplyLocalSimplifications = applyLocalSimplifications;
	}

	@Override
	protected void convert(final Term term) {
		if (term instanceof TermVariable) {
			final Term result = transferTermVariable((TermVariable) term);
			setResult(result);
		} else if (term instanceof ConstantTerm) {
			final Sort sort = transferSort(term.getSort());
			final ConstantTerm ct = (ConstantTerm) term;
			final Term result;
			if (ct.getValue() instanceof BigInteger) {
				result = mScript.numeral((BigInteger) ct.getValue());
			} else if (ct.getValue() instanceof BigDecimal) {
				result = mScript.decimal((BigDecimal) ct.getValue());
			} else if (ct.getValue() instanceof Rational) {
				result = ((Rational) ct.getValue()).toTerm(sort);
			} else if (ct.getValue() instanceof String) {
				final String value = (String) ct.getValue();
				if (value.startsWith("#x")) {
					result = mScript.hexadecimal(value);
				} else if (value.startsWith("#b")) {
					result = mScript.binary(value);
				} else {
					throw new AssertionError("unexpected ConstantTerm (maybe not yet implemented)" + term);
				}
			} else {
				throw new AssertionError("unexpected ConstantTerm (maybe not yet implemented)" + term);
			}
			setResult(result);
		} else {
			super.convert(term);
		}
	}

	TermVariable transferTermVariable(final TermVariable tv) {
		final TermVariable transferResult;
		final Sort sort = transferSort(tv.getSort());
		transferResult = mScript.variable(tv.getName(), sort);
		return transferResult;
	}

	public Sort transferSort(final Sort sort) {
		final Sort[] arguments = transferSorts(sort.getArguments());
		final String[] indices = sort.getIndices();
		return mScript.sort(sort.getName(), indices, arguments);
	}

	public Sort[] transferSorts(final Sort[] sorts) {
		final Sort[] result = new Sort[sorts.length];
		for (int i = 0; i < sorts.length; i++) {
			result[i] = transferSort(sorts[i]);
		}
		return result;
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		final FunctionSymbol fsymb = appTerm.getFunction();
		/*
		 * Note that resultSort must be non-null if and only if we have an explicitly instantiated polymorphic
		 * FunctionSymbol, i.e., a function of the form (as <name> <sort>). Otherwise mScript.term(..) will fail. Note
		 * that for mScript.declareFun(..) we still need the transferred result sort (see below).
		 */
		final Sort resultSort = fsymb.isReturnOverload() ? transferSort(fsymb.getReturnSort()) : null;
		final Term result;
		if (mApplyLocalSimplifications) {
			result = SmtUtils.termWithLocalSimplification(mScript, fsymb, newArgs);
		} else {
			result = mScript.term(fsymb.getName(), appTerm.getFunction().getIndices(), resultSort, newArgs);
		}
		setResult(result);
	}

	@Override
	public void postConvertLet(final LetTerm oldLet, final Term[] newValues, final Term newBody) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void postConvertQuantifier(final QuantifiedFormula old, final Term newBody) {
		final TermVariable[] vars = new TermVariable[old.getVariables().length];
		for (int i = 0; i < old.getVariables().length; i++) {
			vars[i] = transferTermVariable(old.getVariables()[i]);
		}
		final Term result = mScript.quantifier(old.getQuantifier(), vars, newBody);
		setResult(result);
	}

	@Override
	public void postConvertAnnotation(final AnnotatedTerm old, final Annotation[] newAnnots, final Term newBody) {
		final Term result = mScript.annotate(newBody, newAnnots);
		setResult(result);
	}

}
