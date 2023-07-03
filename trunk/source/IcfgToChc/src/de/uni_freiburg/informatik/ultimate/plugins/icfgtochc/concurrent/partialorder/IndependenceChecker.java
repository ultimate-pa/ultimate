/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.partialorder;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.HcGlobalVar;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.HcLocalVar;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.HornClauseBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.ThreadInstance;
import de.uni_freiburg.informatik.ultimate.util.datastructures.SerialProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Utility class that performs independence checks for {@link SleepSetThreadModularHornClauseProvider}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
class IndependenceChecker {
	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final ISymbolicIndependenceRelation<? super IcfgEdge> mIndependence;
	private final IcfgEdgeFactory mEdgeFactory;

	private final Map<Pair<IcfgEdge, IcfgEdge>, Term> mCache = new HashMap<>();

	private final Map<ILocalProgramVar, ILocalProgramVar> mLeftSubstitution;
	private final Map<ILocalProgramVar, ILocalProgramVar> mRightSubstitution;

	public IndependenceChecker(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final ISymbolicIndependenceRelation<? super IcfgEdge> independence) {
		mLogger = services.getLoggingService().getLogger(getClass());
		mMgdScript = csToolkit.getManagedScript();
		mSymbolTable = csToolkit.getSymbolTable();
		mIndependence = independence;
		mEdgeFactory = new IcfgEdgeFactory(new SerialProvider());

		final var localVars = collectLocalVariables(csToolkit);
		mLeftSubstitution = createVariableMapping("~~left~~", localVars);
		mRightSubstitution = createVariableMapping("~~right~~", localVars);
	}

	public Term getIndependenceCondition(final HornClauseBuilder clause, final ThreadInstance thread1,
			final IcfgEdge action1, final ThreadInstance thread2, final IcfgEdge action2) {
		// Hardcoded conditions for line-queue example
		// TODO remove after evaluation
		Term hardcoded = null;
		if ("value := queue[id - 1][read_ptr];".equals(action1.toString())
				&& "queue := queue[0 := queue[0][write_ptr[0] := idx]];".equals(action2.toString())) {
			final var idLeft = mLeftSubstitution.get(mSymbolTable.getLocals(thread1.getTemplateName()).stream()
					.filter(v -> "id".equals(v.getIdentifier())).findAny().get());
			final var readPtrLeft = mLeftSubstitution.get(mSymbolTable.getLocals(thread1.getTemplateName()).stream()
					.filter(v -> "read_ptr".equals(v.getIdentifier())).findAny().get());
			final var writePtr = mSymbolTable.getGlobals().stream().filter(v -> "write_ptr".equals(v.getIdentifier()))
					.findAny().get();
			hardcoded = SmtUtils.or(mMgdScript.getScript(),
					SmtUtils.distinct(mMgdScript.getScript(), idLeft.getTerm(),
							SmtUtils.constructIntValue(mMgdScript.getScript(), BigInteger.ONE)),
					SmtUtils.distinct(mMgdScript.getScript(), readPtrLeft.getTerm(),
							SmtUtils.select(mMgdScript.getScript(), writePtr.getTerm(),
									SmtUtils.constructIntValue(mMgdScript.getScript(), BigInteger.ZERO))));
		} else if ("value := queue[id - 1][read_ptr];".equals(action1.toString())
				&& "queue := queue[id := queue[id][write_ptr[id] := value]];".equals(action2.toString())) {
			final var idLeft = mLeftSubstitution.get(mSymbolTable.getLocals(thread1.getTemplateName()).stream()
					.filter(v -> "id".equals(v.getIdentifier())).findAny().get());
			final var readPtrLeft = mLeftSubstitution.get(mSymbolTable.getLocals(thread1.getTemplateName()).stream()
					.filter(v -> "read_ptr".equals(v.getIdentifier())).findAny().get());
			final var writePtr = mSymbolTable.getGlobals().stream().filter(v -> "write_ptr".equals(v.getIdentifier()))
					.findAny().get();
			hardcoded = SmtUtils.distinct(mMgdScript.getScript(), readPtrLeft.getTerm(),
					SmtUtils.select(mMgdScript.getScript(), writePtr.getTerm(), SmtUtils.minus(mMgdScript.getScript(),
							idLeft.getTerm(), SmtUtils.constructIntValue(mMgdScript.getScript(), BigInteger.ONE))));
		} else if ("queue := queue[id := queue[id][write_ptr[id] := value]];".equals(action1.toString())
				&& "queue := queue[id := queue[id][write_ptr[id] := value]];".equals(action2.toString())) {
			final var idLeft = mLeftSubstitution.get(mSymbolTable.getLocals(thread1.getTemplateName()).stream()
					.filter(v -> "id".equals(v.getIdentifier())).findAny().get());
			final var idRight = mRightSubstitution.get(mSymbolTable.getLocals(thread2.getTemplateName()).stream()
					.filter(v -> "id".equals(v.getIdentifier())).findAny().get());
			hardcoded = SmtUtils.distinct(mMgdScript.getScript(), idLeft.getTerm(), idRight.getTerm());
		} else if ("queue := queue[id := queue[id][write_ptr[id] := value]];".equals(action1.toString())
				&& "value := queue[id - 1][read_ptr];".equals(action2.toString())) {
			final var idRight = mRightSubstitution.get(mSymbolTable.getLocals(thread2.getTemplateName()).stream()
					.filter(v -> "id".equals(v.getIdentifier())).findAny().get());
			final var readPtrRight = mRightSubstitution.get(mSymbolTable.getLocals(thread2.getTemplateName()).stream()
					.filter(v -> "read_ptr".equals(v.getIdentifier())).findAny().get());
			final var writePtr = mSymbolTable.getGlobals().stream().filter(v -> "write_ptr".equals(v.getIdentifier()))
					.findAny().get();
			hardcoded = SmtUtils.distinct(mMgdScript.getScript(), readPtrRight.getTerm(),
					SmtUtils.select(mMgdScript.getScript(), writePtr.getTerm(), SmtUtils.minus(mMgdScript.getScript(),
							idRight.getTerm(), SmtUtils.constructIntValue(mMgdScript.getScript(), BigInteger.ONE))));
		} else if ("queue := queue[0 := queue[0][write_ptr[0] := idx]];".equals(action1.toString())
				&& "value := queue[id - 1][read_ptr];".equals(action2.toString())) {
			final var idRight = mRightSubstitution.get(mSymbolTable.getLocals(thread2.getTemplateName()).stream()
					.filter(v -> "id".equals(v.getIdentifier())).findAny().get());
			final var readPtrRight = mRightSubstitution.get(mSymbolTable.getLocals(thread2.getTemplateName()).stream()
					.filter(v -> "read_ptr".equals(v.getIdentifier())).findAny().get());
			final var writePtr = mSymbolTable.getGlobals().stream().filter(v -> "write_ptr".equals(v.getIdentifier()))
					.findAny().get();
			hardcoded = SmtUtils.or(mMgdScript.getScript(),
					SmtUtils.distinct(mMgdScript.getScript(), idRight.getTerm(),
							SmtUtils.constructIntValue(mMgdScript.getScript(), BigInteger.ONE)),
					SmtUtils.distinct(mMgdScript.getScript(), readPtrRight.getTerm(),
							SmtUtils.select(mMgdScript.getScript(), writePtr.getTerm(),
									SmtUtils.constructIntValue(mMgdScript.getScript(), BigInteger.ZERO))));
		}
		if (hardcoded != null) {
			mLogger.warn(
					"Hardcoded independence condition for '" + action1 + "' and '" + action2 + "' is: " + hardcoded);
			return deinstantiate(clause, thread1, thread2, hardcoded);
		}

		// first check the cache
		final var cached = mCache.get(new Pair<>(action1, action2));
		if (cached != null) {
			return deinstantiate(clause, thread1, thread2, cached);
		}

		// for symmetric relations, check the cache for the symmetric case as well
		if (mIndependence.isSymmetric()) {
			final var symCached = mCache.get(new Pair<>(action2, action1));
			if (symCached != null) {
				// This needs a different deinstantiation than the cases above and below.
				return deinstantiate(clause, thread2, thread1, symCached);
			}
		}

		final var instantiated = getInstantiatedIndependenceCondition(action1, action2);
		return deinstantiate(clause, thread1, thread2, instantiated);
	}

	private Term getInstantiatedIndependenceCondition(final IcfgEdge action1, final IcfgEdge action2) {
		// compute the independence condition
		final var inst1 = instantiate(action1, mLeftSubstitution);
		final var inst2 = instantiate(action2, mRightSubstitution);
		final var condition = mIndependence.getIndependenceCondition(inst1, inst2);
		mLogger.info(
				"instantiated independence condition for '" + action1 + "' and '" + action2 + "' is: " + condition);

		// cache the condition for future queries
		mCache.put(new Pair<>(action1, action2), condition);

		return condition;
	}

	private IcfgEdge instantiate(final IcfgEdge edge, final Map<ILocalProgramVar, ILocalProgramVar> mapping) {
		final var tf = edge.getTransformula();
		final var copyTf = TransFormulaBuilder.constructCopy(mMgdScript, tf, mapping);
		return mEdgeFactory.createInternalTransition(edge.getSource(), edge.getTarget(), null, copyTf);
	}

	private Term deinstantiate(final HornClauseBuilder clause, final ThreadInstance thread1,
			final ThreadInstance thread2, final Term term) {
		final var backSubstitution = new HashMap<TermVariable, Term>();
		addBackSubstitutionMappings(clause, mLeftSubstitution, backSubstitution, thread1);
		addBackSubstitutionMappings(clause, mRightSubstitution, backSubstitution, thread2);

		for (final var global : mSymbolTable.getGlobals()) {
			final var hcVar = new HcGlobalVar(global);
			final var bodyVar = clause.getBodyVar(hcVar);
			backSubstitution.put(global.getTermVariable(), bodyVar.getTermVariable());
		}

		return Substitution.apply(mMgdScript, backSubstitution, term);
	}

	private void addBackSubstitutionMappings(final HornClauseBuilder clause,
			final Map<ILocalProgramVar, ILocalProgramVar> substitution, final Map<TermVariable, Term> backSubstitution,
			final ThreadInstance thread) {
		for (final var local : mSymbolTable.getLocals(thread.getTemplateName())) {
			final var hcVar = new HcLocalVar(local, thread);
			final var bodyVar = clause.getBodyVar(hcVar);
			final var instVar = substitution.get(local);
			backSubstitution.put(instVar.getTermVariable(), bodyVar.getTermVariable());
		}
	}

	private static Set<ILocalProgramVar> collectLocalVariables(final CfgSmtToolkit csToolkit) {
		final var symbolTable = csToolkit.getSymbolTable();
		return csToolkit.getProcedures().stream().flatMap(p -> symbolTable.getLocals(p).stream())
				.collect(Collectors.toSet());
	}

	private Map<ILocalProgramVar, ILocalProgramVar> createVariableMapping(final String prefix,
			final Set<ILocalProgramVar> localVars) {
		final var result = new HashMap<ILocalProgramVar, ILocalProgramVar>();
		for (final var variable : localVars) {
			final var identifier = prefix + variable.getIdentifier();
			final var copy = ProgramVarUtils.constructLocalProgramVar(identifier, variable.getProcedure(),
					variable.getSort(), mMgdScript, null);
			result.put(variable, copy);
		}
		return result;
	}
}
