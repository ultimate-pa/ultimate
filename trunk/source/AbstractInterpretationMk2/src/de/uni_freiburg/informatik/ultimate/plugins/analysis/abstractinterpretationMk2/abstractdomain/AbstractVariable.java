package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain;

import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;

public class AbstractVariable
{
	private final String str;
	private final DeclarationInformation decl;

	@Override
	public int hashCode()
	{
		final int prime = 31;
		int result = 1;
		result = prime * result + ((decl == null) ? 0 : decl.hashCode());
		result = prime * result + ((str == null) ? 0 : str.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj)
	{
		if (this == obj) return true;
		if (obj == null
		   || getClass() != obj.getClass()) 
		{
			return false;
		}
		AbstractVariable other = (AbstractVariable) obj;
		
//		if (decl == null && other.decl != null) return false;		
//		if (!decl.equals(other.decl)) 			return false;
//		if (str == null && other.str != null)   return false;
//		if (! 			return false;
		
		return str.equals(other.str);
	}

	public String getString()
	{
		return str;
	}

	public DeclarationInformation getDeclaration()
	{
		return decl;
	}

	public AbstractVariable(String str, DeclarationInformation decl)
	{
		this.str = str;
		this.decl = decl;
	}

	public String toString()
	{
		return str.toString().concat("+").concat(decl.toString());
	}

}
