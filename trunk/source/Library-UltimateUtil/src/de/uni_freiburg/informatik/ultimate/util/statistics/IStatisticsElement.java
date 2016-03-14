package de.uni_freiburg.informatik.ultimate.util.statistics;

public interface IStatisticsElement {
	
	public Class<?> getDataType();
	
	public Object aggregate(Object o1, Object o2);
	
	public String prettyprint(Object o);
	
	

}
