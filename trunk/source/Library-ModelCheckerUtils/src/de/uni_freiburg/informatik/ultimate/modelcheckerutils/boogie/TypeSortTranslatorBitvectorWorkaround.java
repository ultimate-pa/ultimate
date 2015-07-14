package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.math.BigInteger;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;

/**
 * Translate integers to bit vectors, otherwise call TypeSortTranslator.
 * 
 * @author Thomas Lang
 *
 */
public class TypeSortTranslatorBitvectorWorkaround extends TypeSortTranslator {

	public TypeSortTranslatorBitvectorWorkaround(
			Collection<TypeDeclaration> declarations, Script script,
			boolean blackHoleArrays, IUltimateServiceProvider services) {
		super(declarations, script, blackHoleArrays, services);
	}

	protected Sort constructSort(IType boogieType, BoogieASTNode BoogieASTNode) {
		if (boogieType.equals(PrimitiveType.intType)) {
			BigInteger[] sortIndices = { BigInteger.valueOf(32) };
			return m_Script.sort("BitVec", sortIndices);
		} else {
			return super.constructSort(boogieType, BoogieASTNode);
		}
	}
}
