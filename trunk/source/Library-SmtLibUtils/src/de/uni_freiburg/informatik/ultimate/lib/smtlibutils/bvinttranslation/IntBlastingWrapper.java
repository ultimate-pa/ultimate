/*
 * Copyright (C) 2023 Max Barth (Max.Barth95@gmx.de)
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.bvinttranslation.TranslationConstrainer.ConstraintsForBitwiseOperations;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.DataType.Constructor;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Max Barth (Max.Barth95@gmx.de)
 *
 */
public class IntBlastingWrapper extends WrapperScript {

	public enum IntBlastingMode { RangeBased, CongruenceBased };

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private LBool mExpectedResult;
	private final Script mBvScript = new NoopScript();
	private final Script mIntScript;
	private final ManagedScript mMgdIntScript;
	private final ArrayDeque<Boolean> mOverapproximationTrackingStack = new ArrayDeque<>();
	private final TranslationManager mTm;

	/**
	 * When we use this wrapper for processing SMT files, and want to write
	 * evaluation results, we store the name of the SMT file here.
	 */
	private final String mBenchmarkFilename;
	private final IntBlastingMode mIntBlastingMode;

	/**
	 * If set to true we write a CSV to the current working directory.
	 */
	private static final boolean WRITE_EVALUATION = false;
	private static final String EVALUATION_FILENAME = "IntBlastingWrapper.csv";

	private static final boolean DEBUG_ERROR_IF_UNKNOWN = false;

	public IntBlastingWrapper(final IUltimateServiceProvider services, final ILogger logger, final Script script,
			final IntBlastingMode intBlastingMode,
			final ConstraintsForBitwiseOperations constraintsForBitwiseOperations, final String benchmarkFilename) {
		super(script);
		mServices = services;
		mLogger = logger;
		mIntScript = script;
		mMgdIntScript = new ManagedScript(services, mIntScript);
		mIntScript.setLogic(Logics.ALL);
		mOverapproximationTrackingStack.add(false);

		mTm = new TranslationManager(mMgdIntScript, constraintsForBitwiseOperations,
				(intBlastingMode == IntBlastingMode.CongruenceBased));
		mBenchmarkFilename = benchmarkFilename;
		mIntBlastingMode = intBlastingMode;
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		// copy&paste from NoopScript
		try {
			setLogic(Logics.valueOf(logic));
		} catch (final IllegalArgumentException eLogicUnsupported) {
			/* Logic is not in enumeration */
			throw new UnsupportedOperationException("Logic " + logic + " not supported");
		}
		// no need to do something, calls the other `setLogic` anyway
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		mBvScript.setLogic(logic);
		// TODO: Exception for unsupported logics
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		// We pass all options to mIntScript.
		mIntScript.setOption(opt, value);

	}

	@Override
	public void setInfo(final String info, final Object value) {
		// If the status of the script is known we store in order to ease debugging.
		if (info.equals(":status")) {
			final String valueAsString = (String) value;
			mExpectedResult = LBool.valueOf(valueAsString.toUpperCase());
		} else {
			// We do not pass the status. Because of overapproximation
			// the status may not be correct for the underlying Int solver.
			// We pass all other info strings to mIntScript.
			mIntScript.setInfo(info, value);
		}
	}

	@Override
	public FunctionSymbol getFunctionSymbol(final String constructor) {
		// TODO: Probably unsupported, we will see...
		return mBvScript.getFunctionSymbol(constructor);
	}

	@Override
	public Constructor constructor(final String name, final String[] selectors, final Sort[] argumentSorts)
			throws SMTLIBException {
		// TODO: Probably unsupported, we will see...
		return mBvScript.constructor(name, selectors, argumentSorts);
	}

	@Override
	public DataType datatype(final String typename, final int numParams) throws SMTLIBException {
		// TODO: Probably unsupported, we will see...
		return mBvScript.datatype(typename, numParams);
	}

	@Override
	public void declareDatatype(final DataType datatype, final Constructor[] constrs) throws SMTLIBException {
		// TODO: Probably unsupported, we will see...
		mBvScript.declareDatatype(datatype, constrs);
		throw new UnsupportedOperationException("Cannot yet translate algebraic datatypes");
	}

	@Override
	public void declareDatatypes(final DataType[] datatypes, final Constructor[][] constrs, final Sort[][] sortParams)
			throws SMTLIBException {
		// TODO: Probably unsupported, we will see...
		mBvScript.declareDatatypes(datatypes, constrs, sortParams);
		throw new UnsupportedOperationException("Cannot yet translate algebraic datatypes");
	}

	@Override
	public void declareSort(final String sort, final int arity) throws SMTLIBException {
		mBvScript.declareSort(sort, arity);
		// We declare new sorts also in the int solver
		mIntScript.declareSort(sort, arity);
	}

	@Override
	public void defineSort(final String sort, final Sort[] sortParams, final Sort definition) throws SMTLIBException {
		mBvScript.defineSort(sort, sortParams, definition);

		final Sort[] newSortParams = new Sort[sortParams.length];
		for (int i = 0; i < sortParams.length; i++) {
			newSortParams[i] = translateSort(mIntScript, sortParams[i]);
		}
		final Sort newDefinition = translateSort(mIntScript, definition);
		mIntScript.defineSort(sort, newSortParams, newDefinition);
	}

	@Override
	public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort, final Term definition)
			throws SMTLIBException {
		mBvScript.defineFun(fun, params, resultSort, definition);

		final TermVariable[] newParams = new TermVariable[params.length];
		for (int i = 0; i < params.length; i++) {
			final Sort newParamSort = translateSort(mIntScript, params[i].getSort());
			final TermVariable newTermVariable = mIntScript.variable(params[i].getName(), newParamSort);
			newParams[i] = newTermVariable;
		}
		final Sort newResultSort = translateSort(mIntScript, resultSort);
		final Term definitionWithoutLet = new FormulaUnLet().unlet(definition);
		final Triple<Term, Set<Term>, Boolean> triple;
		try {
			triple = mTm.translateBvtoIntTransferrer(definitionWithoutLet,
				new HistoryRecordingScript(mBvScript), new HistoryRecordingScript(mIntScript));
		} catch (final Throwable th) {
			throw new AssertionError(th);
		}
		final Term newDefinition = SmtUtils.simplify(mMgdIntScript, triple.getFirst(), mServices,
				SimplificationTechnique.POLY_PAC);
		if (triple.getThird()) {
			// there was an overapproximation
			throw new UnsupportedOperationException("We cannot overapproximate in definition of defineFun");
		} else {
			if (!triple.getSecond().isEmpty()) {
				throw new AssertionError("Unknown additional auxiliary variables " + triple.getSecond());
			}
		}
		mIntScript.defineFun(fun, newParams, newResultSort, newDefinition);
	}

	@Override
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort) throws SMTLIBException {
		// FIXME: Declare new function also in Int solver
		// FIXME: Assert in-range assumption immediately

		final Sort[] newParamSorts = new Sort[paramSorts.length];
		for (int i = 0; i < paramSorts.length; i++) {
			newParamSorts[i] = translateSort(mIntScript, paramSorts[i]);
		}
		final Sort newResultSort = translateSort(mIntScript, resultSort);

		mIntScript.declareFun(fun, newParamSorts, newResultSort);
		mBvScript.declareFun(fun, paramSorts, resultSort);
	}

	/**
	 * Translates a bitvector sort to sort Int. Translates parameterized sorts
	 * recursively. E.g., `(Array (_ BitVec 3) Bool)` is translated to `(Array Int
	 * Bool)`.
	 */
	public static Sort translateSort(final Script intScript, final Sort sort) {
		final Sort result;
		if (sort.getName().equals("BitVec")) {
			result = SmtSortUtils.getIntSort(intScript);
		} else {
			final Sort[] oldSorts = sort.getArguments();
			final Sort[] newSorts = new Sort[oldSorts.length];
			for (int i = 0; i < oldSorts.length; i++) {
				newSorts[i] = translateSort(intScript, oldSorts[i]);
			}
			return intScript.sort(sort.getName(), sort.getIndices(), newSorts);
		}
		return result;
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		mBvScript.push(levels);
		mIntScript.push(levels);
		for (int i = 0; i < levels; i++) {
			mOverapproximationTrackingStack.add(false);
		}
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		mBvScript.pop(levels);
		mIntScript.pop(levels);
		for (int i = 0; i < levels; i++) {
			mOverapproximationTrackingStack.removeLast();
		}

	}

	@Override
	public LBool assertTerm(final Term bvTerm) throws SMTLIBException {
		if (!mServices.getProgressMonitorService().continueProcessing()) {
			writeEvalRow(0, "Timeout at beginning of assertTerm");
			throw new ToolchainCanceledException(IntBlastingWrapper.class,
					String.format("assertTerm"));
		}
		final Term bvTermWithoutLet = new FormulaUnLet().unlet(bvTerm);
		final Triple<Term, Set<Term>, Boolean> translationResult;
		try {
			translationResult = mTm.translateBvtoIntTransferrer(bvTermWithoutLet, new HistoryRecordingScript(mBvScript),
					new HistoryRecordingScript(mIntScript));
		} catch (final Throwable th) {
			writeEvalRow(0, th.toString());
			throw new AssertionError(th);
		}
		final Term intTerm = translationResult.getFirst();
		final boolean weDidAnOverapproximation = translationResult.getThird();
		if (weDidAnOverapproximation) {
			mOverapproximationTrackingStack.removeLast();
			mOverapproximationTrackingStack.add(true);
		}
		try {
			final Term simplifiedIntTerm = SmtUtils.simplify(mMgdIntScript, intTerm, mServices,
					SimplificationTechnique.POLY_PAC);
			return mIntScript.assertTerm(simplifiedIntTerm);
		} catch (final Throwable th) {
			writeEvalRow(0, th.toString());
			throw new AssertionError(th);
		}
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		final long startTime = System.nanoTime();
		final LBool intSolverResult = mIntScript.checkSat();
		final long durationNs = System.nanoTime() - startTime;
		final long durationMs = durationNs / 1_000_000;
		// TODO: Compare with mExpectedResult
		final LBool result;
		if (intSolverResult == LBool.SAT && mOverapproximationTrackingStack.contains(true)) {
			// Maybe the result in only SAT because we overapproximated.
			result = LBool.UNKNOWN;
			if (DEBUG_ERROR_IF_UNKNOWN) {
				throw new AssertionError("Overapproximation and SAT, we have to return UNKNOWN!");
			}
		} else {
			result = intSolverResult;
		}
		if (mExpectedResult != null && result != LBool.UNKNOWN && result != mExpectedResult) {
			throw new AssertionError("Result incorrect: expected " + mExpectedResult + " obtained " + result);
		}
		if (DEBUG_ERROR_IF_UNKNOWN && result == LBool.UNKNOWN) {
			throw new AssertionError("Int solver returned UNKNOWN");
		}
		writeEvalRow(durationMs, result.toString());
		return result;
	}

	private void writeEvalRow(final long durationMs, final String result) {
		if (!WRITE_EVALUATION) {
			return;
		}
		try (FileWriter fw = new FileWriter(EVALUATION_FILENAME, true);
				BufferedWriter bw = new BufferedWriter(fw);
				PrintWriter out = new PrintWriter(bw)) {
			out.println(String.format("%s,%s,%s,%s", mBenchmarkFilename, mIntBlastingMode, durationMs, result));
		} catch (final IOException e) {
			throw new AssertionError(e);
		}
	}

	@Override
	public LBool checkSatAssuming(final Term... assumptions) throws SMTLIBException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		// TODO: Probably unsupported, we will see...
		return mBvScript.getAssertions();
	}

	@Override
	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		// TODO: Probably unsupported, we will see...
		return mBvScript.getProof();
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException, UnsupportedOperationException {
		// TODO: Complicated, but we want to support that in the future.
		throw new UnsupportedOperationException();
	}

	@Override
	public Term[] getUnsatAssumptions() throws SMTLIBException, UnsupportedOperationException {
		// TODO: Probably unsupported, we will see...
		return mBvScript.getUnsatAssumptions();
	}

	@Override
	public Map<Term, Term> getValue(final Term[] terms) throws SMTLIBException, UnsupportedOperationException {
		// TODO: Complicated, but we want to support that in the future.
		throw new UnsupportedOperationException();
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException, UnsupportedOperationException {
		// TODO: Probably unsupported, we will see...
		return mBvScript.getAssignment();
	}

	@Override
	public Object getOption(final String opt) throws UnsupportedOperationException {
		// We ask the mIntSolver for the option
		return mIntScript.getOption(opt);
	}

	@Override
	public Object getInfo(final String info) throws UnsupportedOperationException, SMTLIBException {
		// We ask the mIntSolver for the info
		return mIntScript.getInfo(info);
	}

	@Override
	public void exit() {
		mBvScript.exit();
		mIntScript.exit();
	}

	@Override
	public Theory getTheory() {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.getTheory();
	}

	@Override
	public Sort sort(final String sortname, final Sort... params) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.sort(sortname, params);
	}

	@Override
	public Sort sort(final String sortname, final String[] indices, final Sort... params) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.sort(sortname, indices, params);
	}

	@Override
	public Sort[] sortVariables(final String... names) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.sortVariables(names);
	}

	@Override
	public Term term(final String funcname, final Term... params) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.term(funcname, params);
	}

	@Override
	public Term term(final String funcname, final String[] indices, final Sort returnSort, final Term... params)
			throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.term(funcname, indices, returnSort, params);
	}

	@Override
	public TermVariable variable(final String varname, final Sort sort) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.variable(varname, sort);
	}

	@Override
	public Term quantifier(final int quantor, final TermVariable[] vars, final Term body, final Term[]... patterns)
			throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.quantifier(quantor, vars, body, patterns);
	}

	@Override
	public Term let(final TermVariable[] vars, final Term[] values, final Term body) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.let(vars, values, body);
	}

	@Override
	public Term match(final Term dataArg, final TermVariable[][] vars, final Term[] cases,
			final Constructor[] constructors) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.match(dataArg, vars, cases, constructors);
	}

	@Override
	public Term annotate(final Term t, final Annotation... annotations) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.annotate(t, annotations);
	}

	@Override
	public Term numeral(final String num) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.numeral(num);
	}

	@Override
	public Term numeral(final BigInteger num) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.numeral(num);
	}

	@Override
	public Term decimal(final String decimal) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.decimal(decimal);
	}

	@Override
	public Term decimal(final BigDecimal decimal) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.decimal(decimal);
	}

	@Override
	public Term hexadecimal(final String hex) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.hexadecimal(hex);
	}

	@Override
	public Term binary(final String bin) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.binary(bin);
	}

	@Override
	public Term string(final QuotedObject str) throws SMTLIBException {
		// Methods for construction of Term/Sort should only be called by the parser.
		// Unfortunately, we cannot enforce this.
		return mBvScript.string(str);
	}

	@Override
	public Term simplify(final Term term) throws SMTLIBException {
		// TODO: In the future probably an opportunity to set the backtranslation
		throw new UnsupportedOperationException();
	}

	@Override
	public void reset() {
		mBvScript.reset();
		mIntScript.reset();
	}

	@Override
	public void resetAssertions() {
		// TODO: Probably unsupported, we will see...
		mBvScript.resetAssertions();
	}

	@Override
	public Term[] getInterpolants(final Term[] partition) throws SMTLIBException, UnsupportedOperationException {
		// TODO: Complicated, but we want to support that in the future.
		throw new UnsupportedOperationException();
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree)
			throws SMTLIBException, UnsupportedOperationException {
		// TODO: Complicated, but we want to support that in the future.
		throw new UnsupportedOperationException();
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree, final Term proofTree)
			throws SMTLIBException, UnsupportedOperationException {
		// TODO: Complicated, but we want to support that in the future.
		throw new UnsupportedOperationException();
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		// TODO: Complicated, but we want to support that in the future.
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterable<Term[]> checkAllsat(final Term[] predicates) throws SMTLIBException, UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	@Override
	public Term[] findImpliedEquality(final Term[] x, final Term[] y) {
		throw new UnsupportedOperationException();
	}

	@Override
	public QuotedObject echo(final QuotedObject msg) {
		// We pass echos directly to mIntScript
		return mIntScript.echo(msg);
	}

}
