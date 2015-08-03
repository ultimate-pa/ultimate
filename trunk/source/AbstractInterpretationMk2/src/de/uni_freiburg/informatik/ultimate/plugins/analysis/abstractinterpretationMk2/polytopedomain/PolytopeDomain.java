/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain;

import java.math.BigDecimal;
import java.math.BigInteger;

import org.apache.log4j.Logger;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.AbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.signdomain.SignValue.Sign;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IAbstractValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IValueMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.IValueWideningOperator;

/**
 * @author Jan Hättig
 *
 */
public class PolytopeDomain
		implements IAbstractDomain<PolytopeState>
{
	private static final String s_domainID = "POLYTOPE";

	private final Logger m_logger;

	private IAbstractMergeOperator<PolytopeState> mMergeOperator;
	private IAbstractWideningOperator<PolytopeState> mWideningOperator;

	public PolytopeDomain(Logger logger)
	{
		m_logger = logger;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#getMergeOperator()
	 */
	@Override
	public IAbstractMergeOperator<PolytopeState> getMergeOperator()
	{
		return mMergeOperator;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2
	 * .abstractdomain.IAbstractDomainFactory#getWideningOperator()
	 */
	@Override
	public IAbstractWideningOperator<PolytopeState> getWideningOperator()
	{
		return mWideningOperator;
	}

	@Override
	public void setMergeOperator(IAbstractMergeOperator<PolytopeState> mergeOperator)
	{
		mMergeOperator = mergeOperator;

	}

	@Override
	public void setWideningOperator(IAbstractWideningOperator<PolytopeState> wideningOperator)
	{
		mWideningOperator = wideningOperator;
	}

	public static String getDomainID()
	{
		return s_domainID;
	}

	@Override
	public IAbstractState<PolytopeState> createState()
	{
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public IAbstractState<PolytopeState> ApplyExpression(IAbstractState<PolytopeState> state, AbstractVariable target, IType targetType, Expression exp)
	{
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IAbstractState<PolytopeState> ApplyHavoc(IAbstractState<PolytopeState> state, AbstractVariable target, IType targetType)
	{
		// TODO Auto-generated method stub
		return null;
	}
	@Override
	public IAbstractState<PolytopeState> ApplyAssume(IAbstractState<PolytopeState> state, Expression exp)
	{
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean ApplyAssert(IAbstractState<PolytopeState> state, Expression exp)
	{
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public IAbstractState<PolytopeState> createBottom()
	{
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IAbstractState<PolytopeState> createTop()
	{
		// TODO Auto-generated method stub
		return null;
	}
}
