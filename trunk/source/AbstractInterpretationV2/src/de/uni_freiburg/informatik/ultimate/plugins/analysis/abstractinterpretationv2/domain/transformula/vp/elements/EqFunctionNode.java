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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EqFunctionNode extends EqNode {
	
	private final IProgramVarOrConst function;
	private final List<EqNode> args;
	private final Set<IProgramVarOrConst> mAllFunctionSymbols;

	public EqFunctionNode(IProgramVarOrConst function, List<EqNode> args, ManagedScript script) {
		super(function.isGlobal() 
				&& args.stream().map(arg -> arg.mIsGlobal).reduce((b1, b2) -> b1 && b2).get(),
			!(function instanceof IProgramVar)
				&& args.stream().map(arg -> arg.mIsConstant).reduce((b1, b2) -> b1 && b2).get(),
				function instanceof IProgramVar ? 
						((IProgramVar) function).getProcedure() : 
							args.stream()
								.map(arg -> arg.getProcedure())
								.reduce((proc1, proc2) -> proc1 != null ? proc1 : proc2).get());

//		super(function.isGlobal(), !(function instanceof IProgramVar)); // new paradigm: the "topmost function symbol determines isGobal and isConstant.
		 // update: reverted to the old paradigm: a node is constant if all its components are

		this.function = function;
		this.args = args;
		Set<IProgramVar> vars = new HashSet<>();
		if (function instanceof IProgramVar) {
			vars.add((IProgramVar) function);
		}
		for (EqNode arg : args) {
			vars.addAll(arg.getVariables());
		}
		mVariables = Collections.unmodifiableSet(vars);

		mTerm = restoreMultidimensionalSelect(script, function, args);
		
		Set<IProgramVarOrConst> allFunctionSymbols = new HashSet<>();
		allFunctionSymbols.add(function);
		for (EqNode arg : args) {
			allFunctionSymbols.addAll(arg.getAllFunctions());
		}
		mAllFunctionSymbols = Collections.unmodifiableSet(allFunctionSymbols);
	}
	
	@Override
	public IProgramVarOrConst getFunction() {
		return function;
	}

	public List<EqNode> getArgs() {
		return args;
	}

	public String toString() {
		return function.toString() + args.toString();
	}
	
	@Override
	public boolean equals(Object other) {
		return other == this;
//		if (!(other instanceof EqFunctionNode)) {
//			return false;
//		}
//		EqFunctionNode efn = (EqFunctionNode) other;
//		return function.equals(efn.function)
//				&& this.args.equals(efn.args);
	}

//	@Override
//	public Term getTerm(ManagedScript script) {
//	}
	
	private static Term restoreMultidimensionalSelect(ManagedScript script,
			IProgramVarOrConst function, List<EqNode> args) {
		
		Term functionTerm = null;
		if (function instanceof IProgramVar) {
			functionTerm = ((IProgramVar) function).getTermVariable();
		} else {
			functionTerm = function.getTerm();
		}

		assert args.size() > 0;
		if (args.size() == 1) {
			script.lock(function);
			Term result =  script.term(function, "select", functionTerm, args.get(0).getTerm());
			script.unlock(function);
			return result;
		} else {
			List<EqNode> newArgs = args.subList(0, args.size() - 1);
			Term innerTerm = restoreMultidimensionalSelect(script, function, newArgs);
			script.lock(function);
			Term result = script.term(function, "select", 
					innerTerm, 
					args.get(args.size() - 1).getTerm());
			script.unlock(function);
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
	public Collection<IProgramVarOrConst> getAllFunctions() {
		return mAllFunctionSymbols;
	}
}
