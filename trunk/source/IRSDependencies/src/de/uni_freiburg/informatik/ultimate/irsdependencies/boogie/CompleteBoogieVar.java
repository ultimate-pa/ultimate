package de.uni_freiburg.informatik.ultimate.irsdependencies.boogie;

import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;

public class CompleteBoogieVar extends BoogieVar
{
	private static final long serialVersionUID = -7848336493120723097L;

	public CompleteBoogieVar(String identifier, String procedure, IType iType){
		this(identifier,procedure,iType,false);
	}
	
	public CompleteBoogieVar(String identifier, String procedure, IType iType,
			boolean oldvar)
	{
		super(identifier, procedure, iType, oldvar);
	}
	
	@Override
	public String toString()
	{
		return getIdentifier()+":"+getIType();
	}

}
