package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.typeflattening;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayBoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
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
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
class TypeFlattener {

	private final Logger mLogger;
	private final Map<String, PlaceholderTypeDeclaration> mGenericTypes;
	private final ScopedHashMap<String, PlaceholderVarList> mGenericVariables;

	TypeFlattener(final Logger logger) {
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

		unit.setDeclarations(newdecls.toArray(new Declaration[newdecls.size()]));
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
				PlaceholderVarList var = mGenericVariables.get(iexpr.getIdentifier());
				return expr;
			} else if (expr instanceof ArrayAccessExpression) {
				ArrayAccessExpression aaexpr = (ArrayAccessExpression) expr;
				if (aaexpr.getArray() instanceof IdentifierExpression) {
					PlaceholderVarList var = mGenericVariables
							.get(((IdentifierExpression) aaexpr.getArray()).getIdentifier());
					if (var != null) {
						ASTType type = getType(var);
						ArrayBoogieType btype = (ArrayBoogieType) type.getBoogieType();
						Expression[] idxExpr = aaexpr.getIndices();
						BoogieType[] idxTypes = new BoogieType[idxExpr.length];
						for (int i = 0; i < idxExpr.length; ++i) {
							idxTypes[i] = (BoogieType) idxExpr[i].getType();
						}
						ArrayBoogieType newArrayType = btype.instantiate(idxTypes, (BoogieType) aaexpr.getType());
						ASTType newArrayASTType = newArrayType.toASTType(expr.getLocation());
						var.addType(newArrayASTType);
						// TODO: this should be an array access were the struct
						// is the array
						Expression rtr = new StructAccessExpression(expr.getLocation(), newArrayType, aaexpr.getArray(),
								"NameOfNewInnerArrayFieldMangled");
						mLogger.info("Replaced " + BoogiePrettyPrinter.print(expr) + " with "
								+ BoogiePrettyPrinter.print(rtr));
						return rtr;
					}
				}
			} else if (expr instanceof ArrayStoreExpression) {
				ArrayStoreExpression asexpr = (ArrayStoreExpression) expr;
				if (asexpr.getArray() instanceof IdentifierExpression) {
					PlaceholderVarList var = mGenericVariables
							.get(((IdentifierExpression) asexpr.getArray()).getIdentifier());
					if (var != null) {
						ASTType type = getType(var);
						ArrayBoogieType btype = (ArrayBoogieType) type.getBoogieType();
						Expression[] idxExpr = asexpr.getIndices();
						BoogieType[] idxTypes = new BoogieType[idxExpr.length];
						for (int i = 0; i < idxExpr.length; ++i) {
							idxTypes[i] = (BoogieType) idxExpr[i].getType();
						}
						ArrayBoogieType newArrayType = btype.instantiate(idxTypes,
								(BoogieType) asexpr.getValue().getType());
						ASTType newArrayASTType = newArrayType.toASTType(expr.getLocation());
						var.addType(newArrayASTType);
						
						Expression arrayFromStructExpression = new StructAccessExpression(expr.getLocation(), newArrayType,
								asexpr.getArray(), "NameOfNewInnerArrayFieldMangled");
						
						Expression newArrayStoreExpr = new ArrayStoreExpression(expr.getLocation(), newArrayType,
								arrayFromStructExpression, asexpr.getIndices(), asexpr.getValue());
						
						// we have to fill in the actual struct type in the next
						// run
						Expression rtr = new StructConstructor(expr.getLocation(), null,
								new String[] { "NameOfNewInnerArrayFieldMangled" },
								new Expression[] { newArrayStoreExpr });
						mLogger.info("Replaced " + BoogiePrettyPrinter.print(expr) + " with "
								+ BoogiePrettyPrinter.print(rtr));
						return rtr;
					}

				}
				return expr;
			}
			return super.processExpression(expr);
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