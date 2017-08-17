//???safe
/* 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2017-06-15
 * 
 * java.lang.AssertionError
 * at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore.<init>(MultiDimensionalStore.java:82)
 * at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate.<init>(ArrayUpdate.java:104)
 * at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ElimStore3.eliminateSelfUpdates(ElimStore3.java:607)
 * at de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ElimStore3.elim(ElimStore3.java:149)
 * 
 * settings/svcomp2017/automizer/svcomp-Reach-32bit-Automizer_Bitvector.epf
 * toolchains/AutomizerCInline.xml
 * 
 */


typedef struct list {
 int key;
 int *next;
} mlist;
 
void  search_list(mlist *l, int k){
   
  while(    l->key!=1) ;
   
}
void insert_list(mlist *l, int k){

    l->key = 0;
    l->next = 0;

}
void main( ){

  insert_list(0,0);

      search_list(0,0);
  __VERIFIER_error();

}
