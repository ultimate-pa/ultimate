package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

/**
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class EqFunctionNode extends EqNode {
	
	private final IProgramVarOrConst function;
	private final List<EqNode> args;

	public EqFunctionNode(IProgramVarOrConst function, List<EqNode> args) {
		this.function = function;
		this.args = args;
	}
	
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

	@Override
	public Term getTerm(Script script) {
		return restoreMultidimensionalSelect(script, function, args);
	}
	
	private static Term restoreMultidimensionalSelect(Script script,
			IProgramVarOrConst function, List<EqNode> args) {
		
		Term functionTerm = null;
		if (function instanceof IProgramVar) {
			functionTerm = ((IProgramVar) function).getTermVariable();
		} else {
			functionTerm = function.getTerm();
		}

		assert args.size() > 0;
		if (args.size() == 1) {
			return script.term("select", functionTerm, args.get(0).getTerm(script));
		} else {
			List<EqNode> newArgs = args.subList(0, args.size() - 1);
			return script.term("select", 
					restoreMultidimensionalSelect(script, function, newArgs), 
					args.get(args.size() - 1).getTerm(script));
		}
	}

	@Override
	public boolean isLiteral() {
		// a function node is never a literal
		return false;
	}
	
}
