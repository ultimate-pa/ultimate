package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

public class BitUtil{
	
	private static final long MASKS_SINGLE_BIT[] = new long[64];
	static{
		for(int i=0;i<MASKS_SINGLE_BIT.length;i++){
			MASKS_SINGLE_BIT[i] = (((long) 1) << i);
		}
	}
	
	public static long setBit(long bitVector, int bitIndex, boolean value){
        if(value){
            return setBit(bitVector, bitIndex);
        }
        else{
            return unsetBit(bitVector, bitIndex);
        }
    }
	
	public static long setBit(long bitVector, int bitIndex){
        return (bitVector | MASKS_SINGLE_BIT[bitIndex]);
    }
	
	public static long unsetBit(long bitVector, int bitIndex){
        return (bitVector & (~MASKS_SINGLE_BIT[bitIndex]));
    }
	
	public static int getNextSetBit(long bitVector, int offset){
        for(int i=offset;i<64;i++){
            if(getBit(bitVector, i)){
            	return i;
            }
        }
        return -1;
    }
	
	public static boolean getBit(long bitVector, int bitIndex){
        return ((bitVector & MASKS_SINGLE_BIT[bitIndex]) != 0);
    }
	
	public static String getText(long bitVector){
        String text = "";
        for(int i=0;i<64;i++){
            long currentBit = (bitVector & 1);
            text += ((currentBit == 1)?1:0);
            bitVector >>>= 1;
        }
        return text;
    }
}
