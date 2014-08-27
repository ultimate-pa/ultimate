package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.boogie;

import java.util.Hashtable;

import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;

public class ScopedBoogieVarBuilder {

	private final BoogieSymbolTable mSymbolTable;
	private final Hashtable<VariableUID, ScopedBoogieVar> mVarCache;

	public ScopedBoogieVarBuilder(BoogieSymbolTable table) {
		mSymbolTable = table;
		mVarCache = new Hashtable<>();
	}

	public ScopedBoogieVar getScopedBoogieVar(VariableLHS lhs) {
		return getScopedBoogieVar(lhs.getIdentifier(), lhs.getDeclarationInformation());
	}

	public ScopedBoogieVar getScopedBoogieVar(IdentifierExpression identifier) {
		return getScopedBoogieVar(identifier.getIdentifier(), identifier.getDeclarationInformation());

	}

	private ScopedBoogieVar getScopedBoogieVar(String identifier, DeclarationInformation info) {
		VariableDeclaration decl = (VariableDeclaration) mSymbolTable.getDeclaration(identifier,
				info.getStorageClass(), info.getProcedure());
		VariableUID uid = new VariableUID(decl, identifier);
		
		ScopedBoogieVar rtr = mVarCache.get(uid);
		if (rtr == null) {
			rtr = new ScopedBoogieVar(identifier, decl, info);
			mVarCache.put(uid, rtr);
		}
		return rtr;
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
