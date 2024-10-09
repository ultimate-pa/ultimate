/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.util.Collections;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.SmtFreePredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;

/**
 * Used to transfer data structures involving program variables between {@link Script} instances.
 *
 * When using a {@link TermTransferrer} to transfer {@link IPredicate}s or {@link TransFormula}s, one must keep track of
 * the transferred {@link IProgramVar} instances. This class combines a {@link TermTransferrer} with a cache of
 * transferred program variables.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class TransferrerWithVariableCache {
	private final ManagedScript mTargetScript;
	private final TermTransferrer mTransferrer;
	private final TermTransferrer mBackTransferrer;

	// Predicate factory used for predicates that belong to the target script.
	private final SmtFreePredicateFactory mTargetFactory;

	// Predicate factory used for backtransferring predicates to the source script.
	private final SmtFreePredicateFactory mSourceFactory;

	private final BidirectionalMap<IProgramVarOrConst, IProgramVarOrConst> mCache = new BidirectionalMap<>();
	private final BidirectionalMap<IPredicate, IPredicate> mPredicateCache = new BidirectionalMap<>();

	/**
	 * Create a new transferrer.
	 *
	 * @param sourceScript
	 *            The script from which terms are transferred
	 * @param targetScript
	 *            The script to which terms are transferred
	 * @param sourceFactory
	 *            A predicate factory to be used if predicates are transferred back from the target script to the source
	 *            script. May be {@code null} if no predicates will be transferred back.
	 */
	public TransferrerWithVariableCache(final Script sourceScript, final ManagedScript targetScript,
			final SmtFreePredicateFactory sourceFactory) {
		this(sourceScript, targetScript, new SmtFreePredicateFactory(), sourceFactory);
	}

	public TransferrerWithVariableCache(final Script sourceScript, final ManagedScript targetScript,
			final SmtFreePredicateFactory targetFactory, final SmtFreePredicateFactory sourceFactory) {
		mTargetScript = targetScript;

		final var transferMap = new BidirectionalMap<Term, Term>();
		mTransferrer = new TermTransferrer(sourceScript, targetScript.getScript(), transferMap, false);
		mBackTransferrer = new TermTransferrer(targetScript.getScript(), sourceScript, transferMap.inverse(), false);

		mTargetFactory = targetFactory;
		mSourceFactory = sourceFactory;
	}

	public IProgramVar transferProgramVar(final IProgramVar oldPv) {
		return (IProgramVar) mCache.computeIfAbsent(oldPv,
				x -> ProgramVarUtils.transferProgramVar(mTransferrer, oldPv));
	}

	public IProgramConst transferProgramConst(final IProgramConst oldPc) {
		return (IProgramConst) mCache.computeIfAbsent(oldPc,
				x -> ProgramVarUtils.transferProgramConst(mTransferrer, oldPc));
	}

	public Set<IProgramVar> transferVariables(final Set<IProgramVar> vars) {
		return vars.stream().map(this::transferProgramVar).collect(Collectors.toSet());
	}

	public UnmodifiableTransFormula transferTransFormula(final UnmodifiableTransFormula tf) {
		return TransFormulaBuilder.transferTransformula(this, mTargetScript, tf, true);
	}

	public IPredicate transferPredicate(final IPredicate predicate) {
		return mPredicateCache.computeIfAbsent(predicate, this::transferPredicateHelper);
	}

	private BasicPredicate transferPredicateHelper(final IPredicate predicate) {
		if (!predicate.getFuns().isEmpty()) {
			throw new UnsupportedOperationException("Implement support for transferring functions");
		}
		final Set<IProgramVar> variables = transferVariables(predicate.getVars());
		final Term transferredFormula = transferTerm(predicate.getFormula());
		final Term transferredClosed = transferTerm(predicate.getClosedFormula());
		return mTargetFactory.construct(serial -> new BasicPredicate(serial, transferredFormula, variables,
				Collections.emptySet(), transferredClosed));
	}

	public <T extends Term> T transferTerm(final T term) {
		return (T) mTransferrer.transform(term);
	}

	public IIcfgSymbolTable transferSymbolTable(final IIcfgSymbolTable symbolTable, final Set<String> procs) {
		final var result = new DefaultIcfgSymbolTable();

		for (final var glob : symbolTable.getGlobals()) {
			result.add(transferProgramVar(glob));
		}
		for (final var proc : procs) {
			for (final var loc : symbolTable.getLocals(proc)) {
				result.add(transferProgramVar(loc));
			}
		}
		for (final var constant : symbolTable.getConstants()) {
			result.add(transferProgramConst(constant));
		}

		result.finishConstruction();
		return result;
	}

	public TermTransferrer getTransferrer() {
		return mTransferrer;
	}

	public IPredicate backTransferPredicate(final IPredicate predicate) {
		return mPredicateCache.inverse().computeIfAbsent(predicate, this::backTransferPredicateHelper);
	}

	private BasicPredicate backTransferPredicateHelper(final IPredicate predicate) {
		if (!predicate.getFuns().isEmpty()) {
			throw new UnsupportedOperationException("Implement support for transferring functions");
		}
		final Set<IProgramVar> variables = backTransferVariables(predicate.getVars());
		final Term transferredFormula = backTransferTerm(predicate.getFormula());
		final Term transferredClosed = backTransferTerm(predicate.getClosedFormula());
		return mSourceFactory.construct(serial -> new BasicPredicate(serial, transferredFormula, variables,
				Collections.emptySet(), transferredClosed));
	}

	private Term backTransferTerm(final Term term) {
		return mBackTransferrer.transform(term);
	}

	private IProgramVar backTransferProgramVar(final IProgramVar oldPv) {
		// We rely on the assumption that the program variable was created by this transferrer.
		// We do not create new program variables belonging to the source script.
		return (IProgramVar) mCache.inverse().get(oldPv);
	}

	private Set<IProgramVar> backTransferVariables(final Set<IProgramVar> vars) {
		return vars.stream().map(this::backTransferProgramVar).collect(Collectors.toSet());
	}
}
