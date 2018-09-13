package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;

/**
 * Represents the signature of a Boogie procedure in simpler terms, than the Procedure class.
 * Used for tracking the signatures of the dispatching procedures for function pointer calls. (ref. FunctionHandler)
 * 
 * @author Alexander Nutz
 */
public class ProcedureSignature {
	private final ArrayList<ASTType> mInParams = new ArrayList<>();
	private final ASTType mReturnType;
	private final boolean mTakesVarArgs;
	private final String mStringRepresentation;
	
	public ProcedureSignature(final Dispatcher main, final CFunction cf) {
		for (final CDeclaration ip : cf.getParameterTypes()) {
			final ASTType type = main.mTypeHandler.cType2AstType(LocationFactory.createIgnoreCLocation(), ip.getType());
			mInParams.add(type);
		}
		if (cf.getResultType() instanceof CPrimitive && ((CPrimitive) cf.getResultType()).getType() == CPrimitives.VOID) {
			mReturnType = null;
		} else {
			mReturnType = main.mTypeHandler.cType2AstType(LocationFactory.createIgnoreCLocation(), cf.getResultType());
		}
		mTakesVarArgs = cf.takesVarArgs();
		mStringRepresentation = buildStringRepresentation();
	}
	
	public ASTType getReturnType() {
		return mReturnType;
	}

	@Override
	public String toString() {
		return mStringRepresentation;
	}
	
	private String buildStringRepresentation() {
		final StringBuilder sb = new StringBuilder();
		sb.append("##fun~");
		String times = "";
		for (int i = 0; i < mInParams.size(); i++) {
			sb.append(times);
			final ASTType inParam = mInParams.get(i);
			sb.append(BoogiePrettyPrinter.print(inParam));
			times = "~X~";
		}
		if (mTakesVarArgs) {
			sb.append("X~varArgs~");
		}
		sb.append("~TO~");
		sb.append(mReturnType != null ? BoogiePrettyPrinter.print(mReturnType) : "VOID");
		return sb.toString();
	}

	@Override
	public boolean equals(final Object o) {
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
		return mStringRepresentation.hashCode();
	}
}
