/*
 * Copyright (C) 2019 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.ISmtDeclarable.IllegalSmtDeclarableUsageException;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.DataType;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;

/**
 * {@link HistoryRecordingScript} is a {@link WrapperScript} that tracks definitions and declarations of functions,
 * sorts and variables of the underlying {@link Script} instance in the order of their occurence as
 * {@link ISmtDeclarable}.
 *
 * {@link ISmtDeclarable} can be used to initialize a new solver instance with the same functions, sorts and variables.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class HistoryRecordingScript extends WrapperScript {

	public final Deque<ISmtDeclarable> mHistory;
	private final Map<String, ISmtDeclarable> mSymbolTable;
	private int mCurrentStackLevel;
	private ManagedScript mMainScript = null;
	public boolean mAfterSynchronisation = false;

	public HashMap<TermVariable, TermVariable> workerTermVariableToMainTermVariable;

	private TermTransferrer mTf = null;

	public HistoryRecordingScript(final Script script) {
		super(script);
		mHistory = new ArrayDeque<>();
		mSymbolTable = new Hashtable<>();
		workerTermVariableToMainTermVariable = new HashMap<>();
		mCurrentStackLevel = 0;
	}

	public void setMainScript(final ManagedScript mainScript) {
		mMainScript = mainScript;
		mTf = new TermTransferrer(mMainScript.getScript(), this);
	}

	public Term transferTermToWorker(final Term mainTerm) {

		if (mTf == null) {
			return mainTerm;
		}
		final Term workerTerm = mTf.transform(mainTerm);
		if (workerTerm.equals(mainTerm)) {
			return workerTerm;
		}
		if (mainTerm instanceof TermVariable) {
			addTermVariableToMap((TermVariable) workerTerm, (TermVariable) mainTerm);
		}
		return workerTerm;
	}

	public Sort transferSortToWorker(final Sort mainSort) {
		if (mTf == null) {
			return mainSort;
		}
		return mTf.transferSort(mainSort);
	}

	public ManagedScript getMainScript() {
		return mMainScript;
	}

	/*
	 * maps for the termvariables for boogievars
	 */
	public void addTermVariableToMap(final TermVariable workerTv, final TermVariable mainTv) {
		assert !workerTv.equals(mainTv);
		workerTermVariableToMainTermVariable.put(workerTv, mainTv);
	}

	public TermVariable getMainTv(final TermVariable workerTv) {
		if (workerTermVariableToMainTermVariable.containsKey(workerTv)) {
			return workerTermVariableToMainTermVariable.get(workerTv);
		} else {
			return (TermVariable) mTf.getTransferMapping().get(workerTv);
		}

	}

	@Override
	public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort, final Term definition)
			throws SMTLIBException {
		mScript.defineFun(fun, params, resultSort, definition);
		insert(DeclarableFunctionSymbol.createFromScriptDefineFun(fun, params, resultSort, definition));
	}

	@Override
	public void resetAssertions() {
		mScript.resetAssertions();

		removeStackLevelsFromHistory(mCurrentStackLevel);
	}

	@Override
	public void reset() {
		mScript.reset();

		mHistory.clear();
		mSymbolTable.clear();
	}

	@Override
	public void defineSort(final String sort, final Sort[] sortParams, final Sort definition) {
		mScript.defineSort(sort, sortParams, definition);

		insert(DeclarableSortSymbol.createFromScriptDefineSort(sort, sortParams, definition));
	}

	@Override
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort) {

		mScript.declareFun(fun, paramSorts, resultSort);

		insert(DeclarableFunctionSymbol.createFromScriptDeclareFun(fun, paramSorts, resultSort));
	}

	@Override
	public void declareSort(final String sort, final int arity) {
		mScript.declareSort(sort, arity);
		insert(DeclarableSortSymbol.createFromScriptDeclareSort(sort, arity));
	}

	@Override
	public void push(final int levels) {
		mScript.push(levels);

		assert levels > 0;
		for (int i = 0; i < levels; ++i) {
			mHistory.push(StackMarker.INSTANCE);
		}
		mCurrentStackLevel += levels;
	}

	@Override
	public void pop(final int levels) {
		mScript.pop(levels);

		removeStackLevelsFromHistory(levels);
	}

	private void removeStackLevelsFromHistory(final int levels) {
		assert levels > 0;
		final Iterator<ISmtDeclarable> iter = mHistory.iterator();
		int markerCount = 0;
		for (int i = 0; i < levels; ++i) {
			while (iter.hasNext()) {
				// TODO: Possibly too expensive!
				final ISmtDeclarable current = iter.next();
				iter.remove();
				if (current == StackMarker.INSTANCE) {
					markerCount++;
					break;
				}
				final ISmtDeclarable old = mSymbolTable.remove(current.getName());
				assert old != null;
			}
		}
		assert markerCount == levels;
		mCurrentStackLevel -= levels;
		if (mCurrentStackLevel < 0) {
			mCurrentStackLevel = 0;
		}
	}

	private void insert(final ISmtDeclarable declarable) {
		mHistory.push(declarable);
		final ISmtDeclarable old = mSymbolTable.put(declarable.getName(), declarable);
		assert old == null : "overwriting already existing symbol in history: " + old;
	}

	/**
	 * Transfers the history from this {@link Script} instance to the given one. This means that all declarations and
	 * definitions recorded by this {@link Script} instance will be redone on the supplied {@link Script} instance,
	 * including {@link Script#push(int)} and {@link Script#pop(int)} operations.
	 *
	 * Note: If the other {@link Script} instance already has a state, this might lead to confusing results or even
	 * crashes (e.g., if symbols are defined twice).
	 *
	 * @param script
	 *            The {@link Script} instance that will receive all definitions and declarations known to this
	 *            {@link Script}.
	 */
	public void transferHistoryFromRecord(final Script script) {
		final Iterator<ISmtDeclarable> iter = mHistory.descendingIterator();
		while (iter.hasNext()) {
			final ISmtDeclarable elem = iter.next();
			if (elem instanceof StackMarker) {
				script.push(1);
				continue;
			}
			elem.defineOrDeclare(script);

		}
	}

	/**
	 * Transfers the history from one {@link Script} instance to another.
	 *
	 * This method will unwrap a {@link HistoryRecordingScript} from the oldScript {@link Script} instance and then
	 * transfer the history to the newScript {@link Script} instance.
	 *
	 * If oldScript has no {@link HistoryRecordingScript} instance, an {@link IllegalSmtDeclarableUsageException} is
	 * thrown.
	 *
	 * @param oldScript
	 *            The script from which the history should be transferred.
	 * @param newScript
	 *            The script instance to which the history should be transferred.
	 * @see #transferHistoryFromRecord(Script)
	 */
	public static void transferHistoryFromRecord(final Script oldScript, final Script newScript) {
		final HistoryRecordingScript hrScript = extractHistoryRecordingScript(oldScript);
		if (hrScript == null) {
			throw new IllegalSmtDeclarableUsageException(
					"There is no " + HistoryRecordingScript.class + " script in " + oldScript);
		}
		hrScript.transferHistoryFromRecord(newScript);
	}

	/**
	 * Try to unwrap the first {@link HistoryRecordingScript} instance from the stack of {@link Script}s represented by
	 * script.
	 *
	 * @param script
	 *            The (potential) stack of scripts
	 * @return A {@link HistoryRecordingScript} instance or null
	 */
	public static HistoryRecordingScript extractHistoryRecordingScript(final Script script) {
		if (script instanceof HistoryRecordingScript) {
			return (HistoryRecordingScript) script;
		}
		if (script instanceof WrapperScript) {
			return ((WrapperScript) script).findBacking(HistoryRecordingScript.class);
		}
		return null;
	}

	/**
	 * @return A map from symbol name to {@link ISmtDeclarable} in an arbitrary order.
	 *
	 *         The map does update when the underlying script changes.
	 */
	public Map<String, ISmtDeclarable> getSymbolTable() {
		return Collections.unmodifiableMap(mSymbolTable);
	}

	@Override
	public String toString() {
		return getClass().getSimpleName() + ": " + mHistory;
	}

	/**
	 * Find the first {@link Script} instance that has the given type or is a subtype of the given type in the stack of
	 * {@link Script} instances represented by this {@link WrapperScript}.
	 *
	 * @param <T>
	 *            The type of {@link Script} to search for.
	 * @param clazz
	 *            The {@link Class} instance representing the type.
	 * @return A {@link Script} instance if one can be found or null.
	 */
	@Override
	@SuppressWarnings("unchecked")
	public <T extends Script> T findBacking(final Class<T> clazz) {
		final Iterator<Script> iter = getScriptIterator();
		while (iter.hasNext()) {
			final Script current = iter.next();
			if (clazz.isAssignableFrom(current.getClass())) {
				return (T) current;
			}
		}
		return null;
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		mScript.setLogic(logic);
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		mScript.setLogic(logic);
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		mScript.setOption(opt, value);
	}

	@Override
	public void setInfo(final String info, final Object value) {
		mScript.setInfo(info, value);
	}

	@Override
	public void declareDatatype(final DataType datatype, final DataType.Constructor[] constrs) throws SMTLIBException {
		mScript.declareDatatype(datatype, constrs);
	}

	@Override
	public void declareDatatypes(final DataType[] datatypes, final DataType.Constructor[][] constrs,
			final Sort[][] sortParams) throws SMTLIBException {
		mScript.declareDatatypes(datatypes, constrs, sortParams);
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		if (Thread.currentThread().isInterrupted()) {
			throw new RuntimeException("Worker Interrupted");
		}
		return mScript.assertTerm(term);
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		if (Thread.currentThread().isInterrupted()) {
			throw new RuntimeException("Worker Interrupted");
		}
		return mScript.checkSat();
	}

	@Override
	public LBool checkSatAssuming(final Term... assumptions) throws SMTLIBException {
		if (Thread.currentThread().isInterrupted()) {
			throw new RuntimeException("Worker Interrupted");
		}
		return mScript.checkSatAssuming(assumptions);
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		return mScript.getAssertions();
	}

	@Override
	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		return mScript.getProof();
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException, UnsupportedOperationException {
		return mScript.getUnsatCore();
	}

	@Override
	public Term[] getUnsatAssumptions() throws SMTLIBException, UnsupportedOperationException {
		return mScript.getUnsatAssumptions();
	}

	@Override
	public Map<Term, Term> getValue(final Term[] terms) throws SMTLIBException, UnsupportedOperationException {
		return mScript.getValue(terms);
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException, UnsupportedOperationException {

		return mScript.getAssignment();
	}

	@Override
	public Object getOption(final String opt) throws UnsupportedOperationException {
		return mScript.getOption(opt);
	}

	@Override
	public Object getInfo(final String info) throws UnsupportedOperationException, SMTLIBException {
		return mScript.getInfo(info);
	}

	@Override
	public void exit() {
		mScript.exit();
	}

	public void exitWorkerOnly() {
		mScript.exit();
	}

	@Override
	public Theory getTheory() {
		return mScript.getTheory();
	}

	@Override
	public Sort sort(final String sortname, final Sort... params) throws SMTLIBException {
		return mScript.sort(sortname, params);
	}

	@Override
	public Sort sort(final String sortname, final String[] indices, final Sort... params) throws SMTLIBException {
		return mScript.sort(sortname, indices, params);
	}

	@Override
	public Sort[] sortVariables(final String... names) throws SMTLIBException {
		return mScript.sortVariables(names);
	}

	@Override
	public DataType.Constructor constructor(final String name, final String[] selectors, final Sort[] argumentSorts)
			throws SMTLIBException {
		return mScript.constructor(name, selectors, argumentSorts);
	}

	@Override
	public DataType datatype(final String typename, final int numParams) throws SMTLIBException {
		return mScript.datatype(typename, numParams);
	}

	@Override
	public Term term(final String funcname, final Term... params) throws SMTLIBException {
		return mScript.term(funcname, params);

	}

	@Override
	public Term term(final String funcname, final String[] indices, final Sort returnSort, final Term... params)
			throws SMTLIBException {
		return mScript.term(funcname, indices, returnSort, params);
	}

	@Override
	public TermVariable variable(final String varname, final Sort sort) throws SMTLIBException {
		return mScript.variable(varname, sort);
	}

	@Override
	public Term quantifier(final int quantor, final TermVariable[] vars, final Term body, final Term[]... patterns)
			throws SMTLIBException {
		return mScript.quantifier(quantor, vars, body, patterns);
	}

	@Override
	public Term let(final TermVariable[] vars, final Term[] values, final Term body) throws SMTLIBException {
		return mScript.let(vars, values, body);
	}

	@Override
	public Term match(final Term dataArg, final TermVariable[][] vars, final Term[] cases,
			final DataType.Constructor[] constructors) throws SMTLIBException {
		return mScript.match(dataArg, vars, cases, constructors);
	}

	@Override
	public Term annotate(final Term t, final Annotation... annotations) throws SMTLIBException {
		return mScript.annotate(t, annotations);
	}

	@Override
	public Term numeral(final String num) throws SMTLIBException {
		return mScript.numeral(num);
	}

	@Override
	public Term numeral(final BigInteger num) throws SMTLIBException {
		return mScript.numeral(num);
	}

	@Override
	public Term decimal(final String decimal) throws SMTLIBException {
		return mScript.decimal(decimal);
	}

	@Override
	public Term decimal(final BigDecimal decimal) throws SMTLIBException {
		return mScript.decimal(decimal);
	}

	@Override
	public Term hexadecimal(final String hex) throws SMTLIBException {
		return mScript.hexadecimal(hex);
	}

	@Override
	public Term binary(final String bin) throws SMTLIBException {
		return mScript.binary(bin);
	}

	@Override
	public Term string(final QuotedObject str) throws SMTLIBException {
		return mScript.string(str);
	}

	@Override
	public Term simplify(final Term term) throws SMTLIBException {
		return mScript.simplify(term);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition) throws SMTLIBException, UnsupportedOperationException {
		return mScript.getInterpolants(partition);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree)
			throws SMTLIBException, UnsupportedOperationException {
		return mScript.getInterpolants(partition, startOfSubtree);
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		return mScript.getModel();
	}

	@Override
	public Iterable<Term[]> checkAllsat(final Term[] predicates) throws SMTLIBException, UnsupportedOperationException {
		return mScript.checkAllsat(predicates);
	}

	@Override
	public Term[] findImpliedEquality(final Term[] x, final Term[] y) {
		return mScript.findImpliedEquality(x, y);
	}

	@Override
	public QuotedObject echo(final QuotedObject msg) {
		return mScript.echo(msg);
	}

	@Override
	public FunctionSymbol getFunctionSymbol(final String constructor) {
		return mScript.getFunctionSymbol(constructor);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree, final Term proofTree)
			throws SMTLIBException, UnsupportedOperationException {
		return mScript.getInterpolants(partition, startOfSubtree, proofTree);

	}

	private static final class StackMarker implements ISmtDeclarable {

		private static final StackMarker INSTANCE = new StackMarker();

		@Override
		public void defineOrDeclare(final Script script) {
			throw new UnsupportedOperationException(
					getClass().getName() + " only marks stacks, it cannot be defined or declared");
		}

		@Override
		public String getName() {
			throw new UnsupportedOperationException();
		}

		@Override
		public String toString() {
			return "StackMarker";
		}

	}
}
