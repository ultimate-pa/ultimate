package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie;

import java.util.HashSet;
import java.util.Hashtable;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;

public class ScopedBoogieVarBuilder {

	private final BoogieSymbolTable mSymbolTable;
	private final Hashtable<VariableUID, ScopedBoogieVar> mVarCache;

	public ScopedBoogieVarBuilder(BoogieSymbolTable table) {
		mSymbolTable = table;
		mVarCache = new Hashtable<>();
	}

	public ScopedBoogieVar getScopedBoogieVar(VariableLHS lhs, TransFormula tf) {
		return getScopedBoogieVar(lhs.getIdentifier(), lhs.getDeclarationInformation(), tf);
	}

	public ScopedBoogieVar getScopedBoogieVar(IdentifierExpression identifier, TransFormula tf) {
		return getScopedBoogieVar(identifier.getIdentifier(), identifier.getDeclarationInformation(), tf);

	}

	private ScopedBoogieVar getScopedBoogieVar(String identifier, DeclarationInformation info, TransFormula tf) {
		VariableDeclaration decl = (VariableDeclaration) mSymbolTable.getDeclaration(identifier,
				info.getStorageClass(), info.getProcedure());
		VariableUID uid = new VariableUID(decl, identifier);

		ScopedBoogieVar rtr = mVarCache.get(uid);
		if (rtr == null) {
			BoogieVar bv = getBoogieVarFromTransformula(identifier, info, tf);
			rtr = new ScopedBoogieVar(identifier, decl, info, bv);
			mVarCache.put(uid, rtr);
		}
		return rtr;
	}

	private BoogieVar getBoogieVarFromTransformula(String identifier, DeclarationInformation info, TransFormula tf) {
		// TODO: Check if this is the "right" way to get the correct BoogieVar

		HashSet<BoogieVar> vars = new HashSet<BoogieVar>();
		vars.add(getBoogieVarFromSet(identifier, info, tf.getInVars().keySet()));
		vars.add(getBoogieVarFromSet(identifier, info, tf.getOutVars().keySet()));
		vars.add(getBoogieVarFromSet(identifier, info, tf.getAssignedVars()));
		vars.remove(null);

		if (vars.size() != 1) {
			throw new UnsupportedOperationException("Could not find matching BoogieVar");
		}
		return vars.iterator().next();
	}

	private BoogieVar getBoogieVarFromSet(String identifier, DeclarationInformation info, Set<BoogieVar> vars) {
		for (BoogieVar in : vars) {
			if (in.getIdentifier().equals(identifier)) {
				if (in.isOldvar()) {
					continue;
				}
				if (in.isGlobal()) {
					return in;
				}
				if (in.getProcedure().equals(info.getProcedure())) {
					return in;
				}
			}
		}
		return null;
	}

	private class VariableUID {

		private VariableDeclaration Declaration;
		private String Identifier;

		public VariableUID(VariableDeclaration decl, String ident) {
			Declaration = decl;
			Identifier = ident;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + getOuterType().hashCode();
			result = prime * result + ((Declaration == null) ? 0 : Declaration.hashCode());
			result = prime * result + ((Identifier == null) ? 0 : Identifier.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			VariableUID other = (VariableUID) obj;
			if (!getOuterType().equals(other.getOuterType()))
				return false;
			if (Declaration == null) {
				if (other.Declaration != null)
					return false;
			} else if (!Declaration.equals(other.Declaration))
				return false;
			if (Identifier == null) {
				if (other.Identifier != null)
					return false;
			} else if (!Identifier.equals(other.Identifier))
				return false;
			return true;
		}

		private ScopedBoogieVarBuilder getOuterType() {
			return ScopedBoogieVarBuilder.this;
		}
	}

}
