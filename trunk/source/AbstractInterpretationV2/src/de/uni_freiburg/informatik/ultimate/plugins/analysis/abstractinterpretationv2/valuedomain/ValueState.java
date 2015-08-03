package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.valuedomain;



import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.AbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain.ScopedAbstractState;

public class ValueState implements IAbstractState<ValueState>
{
	private final ValueDomain mDomain;
	private final HashMap<AbstractVariable, IAbstractValue<?>> mMapping;

	private boolean mIsBottom;
	private boolean mIsTop;
	
	public ValueState(ValueDomain domain, boolean isBottom, boolean isTop)
	{
		mDomain = domain;
		mMapping = new HashMap<AbstractVariable, IAbstractValue<?>>();
		mIsBottom = isBottom;
		mIsTop = isTop;
	}

	@Override
	public boolean isSuper(IAbstractState<ValueState> other)
	{
		// if(other instanceof())
		// ValueState otherValues = (ValueState) other;
		ValueState otherState = (ValueState) other;
		Set<AbstractVariable> otherKeys = otherState.mMapping.keySet();
		for (AbstractVariable var : otherKeys)
		{
			IAbstractValue thisValue = mMapping.get(var);
			if (thisValue == null)
			{
				return false;
			}
			IAbstractValue otherValue = otherState.mMapping.get(var);
			if (otherValue != null && !thisValue.isSuper(otherValue))
			{
				return false;
			}
		}
		return true;
	}

	@Override
	public void DeclareVariable(AbstractVariable variable)
	{
		if (mMapping.containsKey(variable))
		{
			// info: variable is already present
			return;
		}

		mMapping.put(variable, mDomain.getIntValueFactory().makeTopValue());
	}

	@Override
	public void RemoveVariable(AbstractVariable variable)
	{
		if (!mMapping.containsKey(variable))
		{
			// info: variable is already not present in this state
			return;
		}
	}

	@Override
	public IAbstractState<ValueState> copy()
	{
		ValueState copy = new ValueState(mDomain, mIsBottom, mIsTop);
		
		for(Entry<AbstractVariable, IAbstractValue<?>> entry : mMapping.entrySet())
		{
			copy.mMapping.put(entry.getKey(), entry.getValue());			
		}
		
		return copy;
	}

	/**
	 * Assigns the given value to this state
	 * 
	 * @param identifier
	 *            An existing identifier
	 * @param value
	 *            The new value
	 * @return True iff a layer with the given identifier exists so the value
	 *         could be written
	 */
	public void writeValue(AbstractVariable variable, IAbstractValue<?> value)
	{
		mMapping.put(variable, value);
	}

	public IAbstractValue<?> getValue(AbstractVariable variable)
	{
		return mMapping.get(variable);
	}

	public IAbstractValue<?> getValue(String identifier)
	{
		return mMapping.get(new AbstractVariable(identifier, null));
	}

	
	@Override
	public boolean isBottom()
	{
		if(mIsBottom)
		{
			mIsBottom = true;
			return true;
		}
		
		Iterator<Entry<AbstractVariable, IAbstractValue<?>>> it = mMapping.entrySet().iterator();
	    while (it.hasNext()) 
	    {
	        Map.Entry<AbstractVariable, IAbstractValue<?>> pair = (Map.Entry<AbstractVariable, IAbstractValue<?>>)it.next();
	        if(pair.getValue().isBottom())
	        {
	        	// if any variable is bottom, this state is also bottom
	        	mIsBottom = true;
	        	return true;
	        }	        
	    }
	    return false;		
	}

	@Override
	public boolean isTop()
	{
		if(mIsTop)
		{
			mIsTop = true;
			return true;
		}
		
		Iterator<Entry<AbstractVariable, IAbstractValue<?>>> it = mMapping.entrySet().iterator();
	    while (it.hasNext()) 
	    {
	        Map.Entry<AbstractVariable, IAbstractValue<?>> pair = (Map.Entry<AbstractVariable, IAbstractValue<?>>)it.next();
	        if(!pair.getValue().isTop())
	        {
	        	// if any variable is not top, then this state is also not top
	        	mIsTop= true;
	        	return false;
	        }	        
	    }
	    // (if all states are top) 
	    return true;		
	}

	@Override
	public ValueState getConcrete()
	{		
		return this;
	}
}
