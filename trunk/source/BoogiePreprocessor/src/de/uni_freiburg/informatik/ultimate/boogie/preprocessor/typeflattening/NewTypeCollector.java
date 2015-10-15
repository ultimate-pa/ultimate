package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.typeflattening;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
class NewTypeCollector {

	private final Logger mLogger;
	private final Map<String, PlaceholderTypeDeclaration> mGenericTypes;
	private final ScopedHashMap<String, PlaceholderVarList> mGenericVariables;

	NewTypeCollector(final Logger logger) {
		mLogger = logger;
		mGenericTypes = new LinkedHashMap<>();
		mGenericVariables = new ScopedHashMap<>();
	}

	void run(final Unit unit) {
		final List<Declaration> newdecls = new ArrayList<>();

		final FirstRun first = new FirstRun();
		for (final Declaration decl : unit.getDeclarations()) {
			final Declaration newdecl = first.processDeclaration(decl);
			if (newdecl != null) {
				newdecls.add(newdecl);
			}
		}

		final SecondRun second = new SecondRun();
		for (int i = 0; i < newdecls.size(); ++i) {
			newdecls.set(i, second.processDeclaration(newdecls.get(i)));
		}

		// unit.setDeclarations(newdecls.toArray(new
		// Declaration[newdecls.size()]));
		return;
	}

	private boolean isGeneric(final VarList vl) {
		// either the vl has an already defined generic type, or it is of a
		// generic array type
		return isGeneric(vl.getType());
	}

	private boolean isGeneric(final TypeDeclaration typeDecl) {
		final String[] typeParams = typeDecl.getTypeParams();
		if (typeParams.length > 0) {
			return true;
		}

		final ASTType synonyms = typeDecl.getSynonym();
		if (synonyms == null) {
			return false;
		}
		if (synonyms instanceof FakeASTType) {
			return true;
		}
		return isGeneric(synonyms);
	}

	private boolean isGeneric(final ASTType type) {
		if (type instanceof ArrayType) {
			final ArrayType atype = ((ArrayType) type);
			if (atype.getTypeParams().length > 0) {
				return true;
			}
			return isGeneric(atype.getValueType()) || Arrays.stream(atype.getIndexTypes()).anyMatch(this::isGeneric);
		} else if (type instanceof NamedType) {
			final NamedType ntype = (NamedType) type;
			return ntype.getTypeArgs().length > 0 || mGenericTypes.containsKey(ntype.getName());
		} else if (type instanceof StructType) {
			throw new UnsupportedOperationException("Structs should have been resolved already");
		} else if (type instanceof PrimitiveType) {
			return false;
		} else {
			throw new UnsupportedOperationException(
					"Unknown type " + (type == null ? "null" : type.getClass().getSimpleName()));
		}
	}

	private String getTypeName(ASTType atype) {
		if (atype instanceof NamedType) {
			return ((NamedType) atype).getName();
		}
		return null;
	}

	private PlaceholderTypeDeclaration findGenericDeclaration(String typeName) {
		for (final Entry<String, PlaceholderTypeDeclaration> possibleParent : mGenericTypes.entrySet()) {
			if (possibleParent.getKey().equals(typeName)) {
				return possibleParent.getValue();
			}
		}
		return null;
	}

	private ASTType flatten(final ASTType type) {
		if (type instanceof NamedType) {
			final NamedType ntype = (NamedType) type;
			if (ntype.getTypeArgs().length == 0) {
				if (mGenericTypes.containsKey(ntype.getName())) {
					// this is a synonym and it should not be flattened
					return null;
				}
				return ntype;
			}

			final Set<ASTType> types = new HashSet<ASTType>();
			for (final ASTType arg : ntype.getTypeArgs()) {
				final ASTType flattened = flatten(arg);
				if (flattened == null) {
					return null;
				} else {
					types.add(flattened);
				}
			}
			return new NamedType(type.getLocation(), ntype.getName() + getNewTypeName(types), new ASTType[0]);
		} else if (type instanceof PrimitiveType) {
			return type;
		}
		return null;
	}

	private String getNewTypeName(final Set<ASTType> types) {
		final StringBuilder sb = new StringBuilder();
		for (ASTType type : types) {
			if (type instanceof NamedType) {
				sb.append("$").append(((NamedType) type).getName());
			} else if (type instanceof PrimitiveType) {
				sb.append("$").append(((PrimitiveType) type).getName());
			} else {
				throw new UnsupportedOperationException();
			}
		}
		return sb.toString();
	}

	private final class FirstRun extends BoogieTransformer {

		private final Stack<Expression> mExprStack;

		private FirstRun() {
			mExprStack = new Stack<Expression>();
		}

		@Override
		protected Declaration processDeclaration(final Declaration decl) {
			if (decl instanceof FunctionDeclaration || decl instanceof Procedure) {
				mGenericVariables.beginScope();
				final Declaration rtr = super.processDeclaration(decl);
				mGenericVariables.endScope();
				return rtr;
			} else if (decl instanceof TypeDeclaration) {
				final TypeDeclaration tdecl = (TypeDeclaration) decl;
				if (isGeneric(tdecl)) {
					return processGenericTypeDeclaration(tdecl);
				}
				return tdecl;
			}

			return super.processDeclaration(decl);
		}

		@Override
		protected VarList processVarList(final VarList vl) {
			if (isGeneric(vl)) {
				return processGenericVarList(vl);
			}
			return super.processVarList(vl);
		}

		@Override
		protected Body processBody(final Body body) {
			mGenericVariables.beginScope();
			final Body rtr = super.processBody(body);
			mGenericVariables.endScope();
			return rtr;
		}

		@Override
		protected Expression processExpression(Expression expr) {
			if (expr instanceof IdentifierExpression) {
				IdentifierExpression iexpr = (IdentifierExpression) expr;
				PlaceholderVarList type = mGenericVariables.get(iexpr.getIdentifier());
				if (type != null) {
					return instantiate(type, iexpr);
				}
			}
			mExprStack.push(expr);
			final Expression rtr = super.processExpression(expr);
			mExprStack.pop();
			return rtr;
		}

		@SuppressWarnings("unchecked")
		private Expression instantiate(final PlaceholderVarList var, final IdentifierExpression iexpr) {
			mLogger.info(iexpr);
			// it is generic; now we have to try to instantiate it based
			// on the current expression stack

			final ASTType varType = getType(var);
			final IdentifierExpression rtr;
			if (varType instanceof ArrayType) {
				rtr = instantiateArrayType(var, iexpr, (ArrayType) varType, (Stack<Expression>) mExprStack.clone());
			} else {
				rtr = iexpr;
			}

			return rtr;
		}

		/**
		 * Get the asttype of this generic variable (resolving synonyms if
		 * necessary)
		 */
		private ASTType getType(PlaceholderVarList type) {
			final ASTType rtr = type.getType();
			if (rtr instanceof NamedType) {
				final NamedType ntype = (NamedType) rtr;
				final PlaceholderTypeDeclaration ptd = mGenericTypes.get(ntype.getName());
				if (ptd != null) {
					return ptd.getSynonym();
				}
			}
			return rtr;
		}

		private IdentifierExpression instantiateArrayType(final PlaceholderVarList var,
				final IdentifierExpression iexpr, final ArrayType at, final Stack<Expression> stack) {

			// we will generate a new name for the variable in the current scope
			// and also add a type to var, so that we can later generate the
			// matching declaration

			final String[] tparams = at.getTypeParams();
			assert tparams != null && tparams.length > 0;

			final String identifier = "";

			while (!stack.isEmpty()) {
				Expression current = stack.pop();

				if (current instanceof ArrayStoreExpression) {
					final ArrayStoreExpression asexpr = (ArrayStoreExpression) current;

					if (iexpr == asexpr.getArray()) {
						// we want to instantiate the array itself

					}
				}

			}

			return new IdentifierExpression(iexpr.getLocation(), identifier);
		}

		// private ASTType searchStack(final TypeDeclaration decl) throws
		// AssertionError {
		// ASTType newType = null;
		// final Stack<Expression> restore = new Stack<Expression>();
		// while (!mExpressionStack.isEmpty()) {
		// final Expression parentExpr = mExpressionStack.pop();
		// restore.push(parentExpr);
		//
		// if (shouldFlatten(parentExpr.getType()) != null) {
		// continue;
		// }
		// final IType type = parentExpr.getType();
		// if (!(type instanceof BoogieType)) {
		// throw new AssertionError();
		// }
		// final BoogieType btype = (BoogieType) type;
		// newType = btype.toASTType(parentExpr.getLocation());
		// addInstantiation(decl, newType);
		// break;
		// }
		// while (!restore.isEmpty()) {
		// mExpressionStack.push(restore.pop());
		// }
		// return newType;
		// }

		private VarList processGenericVarList(final VarList vl) {
			mLogger.info(vl);
			final PlaceholderVarList rtr = new PlaceholderVarList(vl);
			for (final String id : rtr.getIdentifiers()) {
				mGenericVariables.put(id, rtr);
			}
			return rtr;
		}

		/**
		 * Produces a placeholder typedecl that will be instantiated in
		 * {@link #run(Unit)}.
		 * 
		 * @param tdecl
		 * @return
		 */
		private Declaration processGenericTypeDeclaration(final TypeDeclaration tdecl) {
			mLogger.info(tdecl);
			// a declaration of a generic type will be deleted. If we can, we
			// instantiate it right here
			final PlaceholderTypeDeclaration rtr = new PlaceholderTypeDeclaration(tdecl);

			// either the type has a synonym and we have to look at this, or it
			// has
			// type params and then we need to look at those

			// mark variable names as belonging to instantiatable typedecls
			// in id expr, check variable names

			mGenericTypes.put(rtr.getIdentifier(), rtr);

			return rtr;
		}
	}

	private final class SecondRun extends BoogieTransformer {
		@Override
		protected Declaration processDeclaration(Declaration decl) {
			if (decl instanceof PlaceholderTypeDeclaration) {
				System.out.println();
			}
			return super.processDeclaration(decl);
		}
	}

	private final class PlaceholderTypeDeclaration extends TypeDeclaration {
		private static final long serialVersionUID = 602282055128508050L;
		private Set<ASTType> mTypes;
		private PlaceholderTypeDeclaration mParent;

		public PlaceholderTypeDeclaration(TypeDeclaration tdecl) {
			super(tdecl.getLocation(), tdecl.getAttributes(), tdecl.isFinite(), tdecl.getIdentifier(),
					tdecl.getTypeParams(), tdecl.getSynonym());
			mTypes = new HashSet<>();
			mParent = findParent();
		}

		private void addType(ASTType type) {
			mTypes.add(type);
			if (mParent != null) {
				mParent.addType(type);
			}
		}

		private PlaceholderTypeDeclaration findParent() {
			if (getSynonym() == null) {
				return null;
			}

			final String typeName = getTypeName(getSynonym());
			if (typeName == null) {
				return null;
			}
			return findGenericDeclaration(typeName);
		}
	}

	private final class PlaceholderVarList extends VarList {
		private static final long serialVersionUID = -4964753793362170227L;
		private PlaceholderTypeDeclaration mParent;
		private Set<ASTType> mTypes;

		public PlaceholderVarList(VarList vl) {
			super(vl.getLocation(), vl.getIdentifiers(), vl.getType(), vl.getWhereClause());
			mParent = findParent();
			mTypes = new HashSet<ASTType>();
			addType(flatten(getType()));
		}

		private PlaceholderTypeDeclaration findParent() {
			BoogieType bt = (BoogieType) getType().getBoogieType();
			ASTType atype = bt.toASTType(getLocation());
			String typename = getTypeName(atype);
			if (typename == null) {
				// this might be a generic variable; we have to duplicate it
				// based on its access
				return null;
			}
			return findGenericDeclaration(typename);
		}

		private void addType(ASTType type) {
			if (type == null) {
				return;
			}
			mTypes.add(type);
			if (mParent != null) {
				mParent.addType(type);
			}
		}
	}
}