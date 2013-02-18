package de.uni_freiburg.informatik.ultimate.boogie.type;

import java.util.ArrayList;

/**
 * A Constructed type is a 
 * @author hoenicke
 *
 */
public class ConstructedType extends BoogieType {
	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -2227100606701950977L;
	private final TypeConstructor constr;
	private final BoogieType[] parameters;
	private final BoogieType realType;
	
	ConstructedType(TypeConstructor c, BoogieType[] parameters) {
		this.constr = c;
		this.parameters = parameters;

		boolean changed = false;
		BoogieType[] realParameters = new BoogieType[parameters.length];
		for (int i = 0; i < realParameters.length; i++) {
			realParameters[i] = parameters[i].getUnderlyingType();
			if (realParameters[i] != parameters[i])
				changed = true;
		}
		BoogieType t = c.getSynonym();
		if (t == null) {
			if (changed)
				realType = createConstructedType(constr, realParameters);
			else
				realType = this;
		} else {
			realType = t.getUnderlyingType().substitutePlaceholders(0, realParameters);
		}
	}

	//@Override
	protected BoogieType substitutePlaceholders(int depth, BoogieType[] substType) {
		if (parameters.length == 0)
			return this;
		BoogieType[] newParam = new BoogieType[parameters.length];
		boolean changed = false;
		for (int i = 0; i < parameters.length; i++) {
			newParam[i] = parameters[i].substitutePlaceholders(depth, substType);
			if (newParam[i] != parameters[i])
				changed = true;
		}
		if (!changed)
			return this;
		return createConstructedType(constr, newParam);
	}

	//@Override
	protected BoogieType incrementPlaceholders(int depth, int incDepth) {
		if (parameters.length == 0)
			return this;
		BoogieType[] newParam = new BoogieType[parameters.length];
		boolean changed = false;
		for (int i = 0; i < parameters.length; i++) {
			newParam[i] = parameters[i].incrementPlaceholders(depth, incDepth);
			if (newParam[i] != parameters[i])
				changed = true;
		}
		if (!changed)
			return this;
		return createConstructedType(constr, newParam);
	}

	//@Override
	protected boolean unify(int depth, BoogieType other, BoogieType[] substitution) {
		if (!(other instanceof ConstructedType))
			return false;
		ConstructedType type = (ConstructedType) other;
		if (constr != type.constr)
			return false;
		for (int i = 0; i < parameters.length; i++) {
			if (!parameters[i].unify(depth, type.parameters[i], substitution))
				return false;
		}
		return true;
	}

	protected boolean hasPlaceholder(int minDepth, int maxDepth) {
		for (BoogieType t : parameters) {
			if (t.hasPlaceholder(minDepth, maxDepth))
				return true;
		}
		return false; 
	}

	//@Override
	protected boolean isUnifiableTo(int depth, BoogieType other, ArrayList<BoogieType> subst) {
		if (this == other || other == errorType)
			return true;
		if (!(other instanceof ConstructedType))
			return false;
		ConstructedType type = (ConstructedType) other;
		if (constr != type.constr)
			return false;
		for (int i = 0; i < parameters.length; i++) {
			if (!parameters[i].isUnifiableTo(depth, type.parameters[i], subst))
				return false;
		}
		return true;
	}

	public BoogieType getUnderlyingType() {
		return realType;
	}
	
	public TypeConstructor getConstr() {
		return constr;
	}
	public BoogieType getParameter(int i) {
		return parameters[i];
	}

	/**
	 * Computes a string representation.  It uses depth to compute artificial
	 * names for the placeholders.
	 * @param depth the number of placeholders outside this expression.
	 * @param needParentheses true if parentheses should be set for constructed types
	 * @return a string representation of this type.
	 */
	protected String toString(int depth, boolean needParentheses) {
		if (parameters.length == 0)
			return constr.getName();
		
		StringBuilder sb = new StringBuilder();
		if (needParentheses)
			sb.append("(");
		sb.append(constr.getName());
		for (BoogieType pType: parameters)
			sb.append(" ").append(pType.toString(depth, true));
		if (needParentheses)
			sb.append(")");
		return sb.toString();
	}
	
	//@Override
	public boolean isFinite() {
		if (realType != this)
			return realType.isFinite();
		return constr.isFinite();
	}
}
