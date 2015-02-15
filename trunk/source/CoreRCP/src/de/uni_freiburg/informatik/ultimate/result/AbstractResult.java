package de.uni_freiburg.informatik.ultimate.result;


/**
 * Default implementation of the IResult interface.
 * @author Matthias Heizmann
 */
public abstract class AbstractResult implements IResult {
	
	final protected String mPlugin; 
	
	public AbstractResult(String plugin) {
		super();
		mPlugin = plugin;
	}
	
	@Override
	public final String getPlugin() {
		return mPlugin;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
//		sb.append(getClass().getSimpleName());
//		sb.append(" ");
		sb.append("ShortDescription: ");
		sb.append(getShortDescription());
		sb.append(" ");
		sb.append("LongDescription: ");
		sb.append(getLongDescription());
		return sb.toString();
		
	}

}
