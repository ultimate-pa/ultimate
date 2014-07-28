package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.services.IStorable;

public class IdentifierMapping<K, V> implements IStorable{

	private final static String sIdentifierMappingKey = "CACSL2BoogieTranslatorIdentifierMapping";
	private Map<K, V> mMap;

	@Override
	public void destroy() {
		// TODO Auto-generated method stub
	}
	
	public Map<K,V> getMap(){
		return mMap;
	}
	
	public void setMap(Map<K,V> map){
		mMap = map;
	}
	
	public static String getStorageKey(){
		return sIdentifierMappingKey;
	}

}
