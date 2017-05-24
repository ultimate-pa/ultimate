/*
 * Copyright (C) 2016 Yu-Wen Chen 
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EqFunctionNode extends EqNode {
	
	private final EqFunction mFunction;
	private final List<EqNode> mArgs;
	private final Set<EqFunction> mAllFunctionSymbols;

	@Deprecated
	public EqFunctionNode(EqFunction function, List<EqNode> args, ManagedScript script, 
			EqNodeAndFunctionFactory eqNodeFactory) {
		super(function.isGlobal() 
				&& args.stream().map(arg -> arg.mIsGlobal).reduce((b1, b2) -> b1 && b2).get(),
			!(function instanceof IProgramVar)
				&& args.stream().map(arg -> arg.mIsConstant).reduce((b1, b2) -> b1 && b2).get(),
				VPDomainHelpers.computeProcedure(function, args), 
				eqNodeFactory);

		mFunction = function;
		mArgs = args;
		mVariables = Collections.unmodifiableSet(computeVars(function, args));
		mAllFunctionSymbols = Collections.unmodifiableSet(computeAllFunctions(function, args));

		mTerm = restoreMultidimensionalSelect(script, function, args);
	}
	
	public EqFunctionNode(EqFunction function, List<EqNode> args, Term term, EqNodeAndFunctionFactory eqNodeFactory) {
		super(term, eqNodeFactory);
		
		mFunction = function;
		mArgs = args;
		mAllFunctionSymbols = Collections.unmodifiableSet(computeAllFunctions(function, args));
	}


	private Set<EqFunction> computeAllFunctions(EqFunction function, List<EqNode> args) {
		Set<EqFunction> allFunctionSymbols = new HashSet<>();
		allFunctionSymbols.add(function);
		for (EqNode arg : args) {
			allFunctionSymbols.addAll(arg.getAllFunctions());
		}
		return allFunctionSymbols;
	}

	private Set<IProgramVar> computeVars(EqFunction function, List<EqNode> args) {
		Set<IProgramVar> vars = new HashSet<>();
		if (function instanceof IProgramVar) {
			vars.add((IProgramVar) function);
		}
		for (EqNode arg : args) {
			vars.addAll(arg.getVariables());
		}
		return vars;
	}
	
	@Override
	public EqFunction getFunction() {
		return mFunction;
	}

	@Override
	public List<EqNode> getArgs() {
		return mArgs;
	}

	public String toString() {
		return mFunction.toString() + mArgs.toString();
	}
	
//	@Override
//	public boolean equals(Object other) {
//		return other == this;
////		if (!(other instanceof EqFunctionNode)) {
////			return false;
////		}
////		EqFunctionNode efn = (EqFunctionNode) other;
////		return function.equals(efn.function)
////				&& this.args.equals(efn.args);
//	}

//	@Override
//	public Term getTerm(ManagedScript script) {
//	}
	
	private static Term restoreMultidimensionalSelect(ManagedScript script,
			EqFunction array, List<EqNode> args) {
		
		Term functionTerm = array.getTerm();

		assert args.size() > 0;
		if (args.size() == 1) {
			script.lock(array);
			Term result =  script.term(array, "select", functionTerm, args.get(0).getTerm());
			script.unlock(array);
			return result;
		} else {
			List<EqNode> newArgs = args.subList(0, args.size() - 1);
			Term innerTerm = restoreMultidimensionalSelect(script, array, newArgs);
			script.lock(array);
			Term result = script.term(array, "select", 
					innerTerm, 
					args.get(args.size() - 1).getTerm());
			script.unlock(array);
			return result;
		}
	}

	@Override
	public boolean isLiteral() {
		// a function node is never a literal
		return false;
	}

	@Override
	public boolean isFunction() {
		return true;
	}

	@Override
	public Collection<EqFunction> getAllFunctions() {
		return mAllFunctionSymbols;
	}

	@Override
	public EqNode renameVariables(Map<Term, Term> substitutionMapping) {
		
		final List<EqNode> renamedArgs = mArgs.stream()
				.map(argNode -> argNode.renameVariables(substitutionMapping))
				.collect(Collectors.toList());

		return mEqNodeFactory.getOrConstructEqFunctionNode(mFunction.renameVariables(substitutionMapping), renamedArgs);
	}
}
