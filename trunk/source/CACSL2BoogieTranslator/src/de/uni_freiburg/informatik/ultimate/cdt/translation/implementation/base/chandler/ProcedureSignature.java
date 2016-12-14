package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;

/**
 * Represents the signature of a Boogie procedure in simpler terms, than the Procedure class.
 * Used for tracking the signatures of the dispatching procedures for function pointer calls. (ref. FunctionHandler)
 * 
 * @author Alexander Nutz
 */
public class ProcedureSignature {
	public ArrayList<ASTType> inParams = new ArrayList<>();
	public ASTType returnType = null;
	public boolean takesVarArgs = false;
	
	public ProcedureSignature(Dispatcher main, CFunction cf) {
		for (final CDeclaration ip : cf.getParameterTypes()) {
			final ASTType type = main.mTypeHandler.cType2AstType(LocationFactory.createIgnoreCLocation(), ip.getType());
			inParams.add(type);
		}
		if (cf.getResultType() instanceof CPrimitive && ((CPrimitive) cf.getResultType()).getType() == CPrimitives.VOID) {
			returnType = null;
		} else {
			returnType = main.mTypeHandler.cType2AstType(LocationFactory.createIgnoreCLocation(), cf.getResultType());
		}
		takesVarArgs = cf.takesVarArgs();
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("##fun~");
		String times = "";
		for (int i = 0; i < inParams.size(); i++) {
			sb.append(times);
			sb.append(inParams.get(i).toString());
			times = "~X~";
		}
		if (takesVarArgs) {
			sb.append("X~varArgs~");
		}
		sb.append("~TO~");
		sb.append(returnType != null ? returnType.toString() : "VOID");
		return sb.toString();
	}

	@Override
	public boolean equals(Object o) {
//		if (!(o instanceof ProcedureSignature)) {
//			return false;
//		}
//		ProcedureSignature other = (ProcedureSignature) o;
//		if (this.inParams.size() != other.inParams.size())
//			return false;
//		boolean result = true;
//		result &= (this.returnType != null && this.returnType.equals(other.returnType)) || (this.returnType == null || other.returnType == null);
//
//		for (int i = 0; i < inParams.size(); i++)
//			result &= this.inParams.get(i).equals(other.inParams.get(i));
//		result &= this.takesVarArgs == other.takesVarArgs;
//		return result;
		return toString().equals(o.toString());
	}

	@Override
	public int hashCode() {
//		int result = returnType != null ? HashUtils.hashJenkins(31, returnType) : 31;
//		for (int i = 0; i < inParams.size(); i++) 
//			result += HashUtils.hashJenkins(result, inParams.get(i));
//		result = HashUtils.hashJenkins(result, takesVarArgs);
//		return result;
		return 0;
	}
}
