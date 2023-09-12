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
package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.FunctionDefinition;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.ModelDescription;
import de.uni_freiburg.informatik.ultimate.util.datastructures.BidirectionalMap;

/**
 * A class to transfer CHC systems between scripts, and to transfer back the results of CHC satisfiability checks.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class ChcTransferrer {
	private final Script mOriginalScript;
	private final ManagedScript mTargetScript;

	private final HcSymbolTable mOriginalSymbolTable;
	private final HcSymbolTable mTargetSymbolTable;

	private final TermTransferrer mTransferrer;
	private final TermTransferrer mBackTransferrer;

	private final BidirectionalMap<Term, Term> mTransferMap = new BidirectionalMap<>();
	private final BidirectionalMap<HcPredicateSymbol, HcPredicateSymbol> mPredMapping = new BidirectionalMap<>();
	private final BidirectionalMap<HornClause, HornClause> mClauseMapping = new BidirectionalMap<>();

	public ChcTransferrer(final Script originalScript, final ManagedScript targetScript,
			final HcSymbolTable symbolTable) {
		mOriginalScript = originalScript;
		mTargetScript = targetScript;
		mTransferrer = new TermTransferrer(originalScript, targetScript.getScript(), mTransferMap, false);
		mBackTransferrer = new TermTransferrer(targetScript.getScript(), originalScript, mTransferMap.inverse(), false);

		mOriginalSymbolTable = symbolTable;
		mTargetSymbolTable = transfer(symbolTable);
	}

	public HornAnnot transfer(final HornAnnot annot) {
		assert annot.getSymbolTable() == mOriginalSymbolTable;
		final var clauses = annot.getHornClauses().stream().map(this::transfer).collect(Collectors.toList());
		return new HornAnnot(annot.getFileName(), mTargetScript, mTargetSymbolTable, clauses, annot.hasCheckSat(),
				annot.getChcCategoryInfo());
	}

	private HcSymbolTable transfer(final HcSymbolTable symbolTable) {
		final var transferredTable = new HcSymbolTable(mTargetScript);
		// TODO transfer components?
		return transferredTable;
	}

	public HcPredicateSymbol transfer(final HcPredicateSymbol predicate) {
		return mPredMapping.computeIfAbsent(predicate, p -> {
			final var sorts =
					p.getParameterSorts().stream().map(mTransferrer::transferSort).collect(Collectors.toList());
			return mTargetSymbolTable.getOrConstructHornClausePredicateSymbol(p.getName(), sorts);
		});
	}

	public <T extends HcVar> T transfer(final T var) {
		if (var instanceof HcBodyAuxVar) {
			throw new UnsupportedOperationException("HcBodyAuxVar not yet supported");
		}
		if (var instanceof HcBodyVar) {
			return (T) transfer((HcBodyVar) var);
		}
		if (var instanceof HcHeadVar) {
			return (T) transfer((HcHeadVar) var);
		}
		throw new AssertionError(
				"Unknown type of variable: " + (var == null ? "null" : var.getClass().getSimpleName()));
	}

	public HcBodyVar transfer(final HcBodyVar var) {
		return transferOld(var, mTargetSymbolTable::getOrConstructBodyVar);
	}

	public HcHeadVar transfer(final HcHeadVar var) {
		return transfer(var, mTargetSymbolTable::getOrConstructHeadVar);
	}

	private interface IHcVarConstructor<T> {
		T getOrConstruct(HcPredicateSymbol pred, int index, Sort sort, Object identifier);
	}

	private <T extends HcPredVar> T transfer(final T variable, final IHcVarConstructor<T> constructor) {
		final var optPredicate = mPredMapping.entrySet().stream()
				.filter(e -> HornUtilConstants.sanitizePredName(e.getKey().getName()).equals(variable.getProcedure()))
				.findAny();
		assert optPredicate.isPresent() : "Could not find predicate for " + variable;
		final var predicate = optPredicate.get().getValue();

		final var sort = mTransferrer.transferSort(variable.getSort());
		final var copy = constructor.getOrConstruct(predicate, variable.getIndex(), sort, variable);

		final var oldMapping = mTransferrer.getTransferMapping().get(variable.getTermVariable());
		if (oldMapping != null && oldMapping != copy.getTermVariable()) {
			throw new IllegalStateException("Variable already mapped: " + variable);
		}
		mTransferrer.getTransferMapping().put(variable.getTermVariable(), copy.getTermVariable());
		return copy;
	}

	@Deprecated
	private <T extends HcVar> T transferOld(final T var, final BiFunction<T, Sort, T> getOrConstruct) {
		final var copy = getOrConstruct.apply(var, mTransferrer.transferSort(var.getSort()));
		final var oldMapping = mTransferrer.getTransferMapping().get(var.getTermVariable());
		if (oldMapping != null && oldMapping != copy.getTermVariable()) {
			throw new IllegalStateException("Variable already mapped: " + var);
		}
		mTransferrer.getTransferMapping().put(var.getTermVariable(), copy.getTermVariable());
		return copy;
	}

	public HornClause transfer(final HornClause clause) {
		return mClauseMapping.computeIfAbsent(clause, c -> {
			// head is transferred first, so all HcHeadVars exist when body arguments and constraint are transferred
			final HcPredicateSymbol head;
			final List<HcHeadVar> headVars;
			if (!clause.isHeadFalse()) {
				head = transfer(clause.getHeadPredicate());
				headVars =
						clause.getTermVariablesForHeadPred().stream().map(this::transfer).collect(Collectors.toList());
			} else {
				head = null;
				headVars = null;
			}

			// transfer body
			final var bodyPreds = clause.getBodyPredicates().stream().map(this::transfer).collect(Collectors.toList());
			final var bodyVars = clause.getBodyVariables().stream().map(this::transfer).collect(Collectors.toSet());
			final var bodyArgs = clause.getBodyPredToArgs().stream()
					.map(args -> args.stream().map(this::transfer).collect(Collectors.toList()))
					.collect(Collectors.toList());

			final var constraint = transfer(clause.getConstraintFormula());
			if (clause.isHeadFalse()) {
				return new HornClause(mTargetSymbolTable, constraint, bodyPreds, bodyArgs, bodyVars);
			}

			return new HornClause(mTargetSymbolTable, constraint, head, headVars, bodyPreds, bodyArgs, bodyVars);
		});
	}

	private Term transfer(final Term term) {
		return mTransferrer.transform(term);
	}

	public ChcSolution transferBack(final ChcSolution solution) {
		switch (solution.getSatisfiability()) {
		case UNKNOWN:
			// nothing to transfer
			return solution;
		case SAT:
			final var originalModel = solution.getModel();
			final var model = originalModel == null ? null : transferBack(originalModel);
			return ChcSolution.sat(model);
		case UNSAT:
			final var originalDerivation = solution.getDerivation();
			final var derivation = originalDerivation == null ? null : transferBack(originalDerivation);
			final var originalUnsatCore = solution.getUnsatCore();
			final var unsatCore = originalUnsatCore == null ? null : transferBack(originalUnsatCore);
			return ChcSolution.unsat(derivation, unsatCore);
		}
		throw new AssertionError("unknown satisfiability value: " + solution.getSatisfiability());
	}

	public Model transferBack(final Model model) {
		if (!(model instanceof ModelDescription)) {
			// TODO support other types of models by wrapping in a "TransferredModel" class?
			throw new UnsupportedOperationException("Can currently only transfer models of type ModelDescription");
		}
		return transferBack((ModelDescription) model);
	}

	private ModelDescription transferBack(final ModelDescription model) {
		final var functions = new HashSet<FunctionDefinition>();
		for (final var func : model.getDefinedFunctions()) {
			if (!isHcPredicate(func)) {
				continue;
			}
			final var funcSym = mOriginalScript.getFunctionSymbol(func.getName());
			final var funDesc = model.getFunctionDefinition(func.getName());
			final var params = Arrays.stream(funDesc.getParams()).map(this::transferBack).toArray(TermVariable[]::new);
			final var body = transferBack(funDesc.getBody());
			functions.add(new FunctionDefinition(funcSym, params, body));
		}
		return new ModelDescription(functions);
	}

	private boolean isHcPredicate(final FunctionSymbol fun) {
		return mPredMapping.values().stream().anyMatch(p -> p.getFunctionSymbol().equals(fun));
	}

	public Derivation transferBack(final Derivation derivation) {
		final var predicate = transferBack(derivation.getPredicate());
		final var arguments = derivation.getArguments().stream().map(this::transferBack).collect(Collectors.toList());
		final var clause = transferBack(derivation.getClause());
		final var children = derivation.getChildren().stream().map(this::transferBack).collect(Collectors.toList());
		return new Derivation(predicate, arguments, clause, children);
	}

	public Set<HornClause> transferBack(final Set<HornClause> unsatCore) {
		return unsatCore.stream().map(this::transferBack).collect(Collectors.toSet());
	}

	public HornClause transferBack(final HornClause clause) {
		if (!mClauseMapping.containsValue(clause)) {
			throw new IllegalArgumentException("Clause was not transferred by this instance: " + clause);
		}
		return mClauseMapping.inverse().get(clause);
	}

	public HcPredicateSymbol transferBack(final HcPredicateSymbol predicate) {
		if (!mPredMapping.containsValue(predicate)) {
			throw new IllegalArgumentException("Predicate symbol was not transferred by this instance: " + predicate);
		}
		return mPredMapping.inverse().get(predicate);
	}

	private TermVariable transferBack(final TermVariable tv) {
		return (TermVariable) mTransferMap.inverse().computeIfAbsent(tv,
				y -> mOriginalScript.variable(((TermVariable) y).getName(), transferBack(y.getSort())));
	}

	private Term transferBack(final Term term) {
		return mBackTransferrer.transform(term);
	}

	private Sort transferBack(final Sort sort) {
		return mBackTransferrer.transferSort(sort);
	}

	public Script getSourceScript() {
		return mOriginalScript;
	}

	public Script getTargetScript() {
		return mTargetScript.getScript();
	}
}
