/* Symbolic Reliability Algorithm (SYREL)  2000.11.29 Tatsuhiro Tsuchiya */
/*  modified by Tatsuhiro Tsuchiya on 2004.10.21  */
/*  modified by Tatsuhiro Tsuchiya on 2004.10.22  */

/* usage: syrel < datafile */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#define BYTESIZE 8
#define MAX_TREES (int)20000
#define MAX_LENGTH (int) 64 /* must be equal to sizeof(long long int) */
#define MAX_CUTS (int)10000

#define MAX_add (int)10000
#define FIN (int)-100

typedef unsigned long long int PATH;

PATH trees[MAX_TREES];
double reliab[MAX_LENGTH];

int length; /* maximum length of tree */
int number; /* total number of trees */

PATH mcset[MAX_TREES];
PATH mcut[MAX_CUTS];

int no_mcset; /* number of minimal conditional sets */

PATH cand_cut;    /* used for evaluating cutsets */
int corres[MAX_LENGTH];
int no_cuts; /* number of minimal conditional sets */

struct list_cuts
{
  PATH cut;
  struct list_cuts *next;
};

struct list_cuts *cuts[MAX_CUTS/2 + 1];

int Found[MAX_LENGTH+1];

/* Disjoint and Calculation */
/* subgraphs + reliabilities */

/* component  0 - 63: 0000000....001 -> component 0,
   0000000....010 -> component 1 */

double Compute_Found(void);
double Disjoint_Procedure(void);
void Cutset_Evaluate(void);
void Free_Cut_List(struct list_cuts *);
void Set_Bit(PATH *, int);
void Reset_Bit(PATH *, int);
int Check_Bit(PATH *, int);
double Prob_Up_Path(PATH *);
double Job(int);


double Compute_Found()
{
  int c;
  double tmp_prob = 1;

  for(c=1;c<=length;c++){

    if(Found[c] == 1)
      tmp_prob = tmp_prob * (1- reliab[c-1]);

    if(Found[c] == 0)
      tmp_prob = tmp_prob * reliab[c-1];
  }
  return tmp_prob;
}

double Disjoint_Procedure()
{
  int m,i,j,k, a,b,c, nad, disjoint;
  int S[MAX_CUTS+1][MAX_LENGTH+1];

  int PD[MAX_add+1][MAX_LENGTH+1];
  int X[MAX_LENGTH+1];

  int add[MAX_add+1][MAX_LENGTH+1];
  double Prob = 0;

  if(no_cuts > MAX_CUTS)
    {
      fprintf(stderr, "exceeded limit on number of cutsets\n");
      exit(-1);
    }

  for(i=1; i <= no_cuts; i++)
    for(j=1; j<=length; j++)
      if((mcut[i-1] & ((unsigned long long int) 1 << (j-1)))!= 0)
	S[i][j] = 1;
      else
	S[i][j] = -1;

  /* Step 1 */
  for(c=1; c<=length; c++)
    Found[c] = S[1][c];
  Prob += Compute_Found();

  /* Step 2 */
  for(k=2; k<=no_cuts; k++)
    {
      /* Step 3 */
      for(a=1; a<=length; a++)
	PD[1][a] = S[k][a];
      PD[2][1] = FIN;

      /* Step 4 */
      for(j=1;j<=k-1;j++)
	{
	  nad = 0;
	  /* Step 5 */
	  for(i=1; PD[i][1] != FIN; i++)
	   {
	     /* Compare PD[i][] with S[j][]*/
	     
	     X[1] = FIN;
	     disjoint = 0;
	     for(m=1;m<=length;m++)
	       {
		 if(((S[j][m]==1)&&(PD[i][m] == 0))||
		    ((S[j][m]==0)&&(PD[i][m] == 1)))
		   {
		     /* disjoint */
		     disjoint =1;
		     break;
		   }
		 if((S[j][m]==1)&&(PD[i][m] < 0))
		   {
		     a = 1;
		     while(X[a] != FIN)
		       a++;
		     X[a] = m;
		     X[a+1] = FIN;
		   }
	       }
	     if(disjoint == 1 )
	       {
		 nad++;

		 if (nad > MAX_add)
		   exit(-1);

		 for(a=1;a<=length;a++)
		   add[nad][a]=PD[i][a];
	       }
	     else
	       {
		 if(X[1]!=FIN)/* replace */
		   {
		     a=1;
		     while(X[a]!=FIN)
		       {
			 nad++;
			 
			 if (nad > MAX_add)
			   exit(-1);

			 for(b=1;b<=length;b++)
			   add[nad][b]=PD[i][b];
			 
			 for(b=1;b<a;b++)
			   add[nad][X[b]]=1;
			 add[nad][X[a]] = 0;
			 a++;
		       }
		   }
	       }
	   }
	  for(i=1;i<=nad;i++)
	    for(a=1;a<=length;a++)
	      PD[i][a]=add[i][a];
	  PD[nad+1][1] = FIN;
	}
      /* step 6 */
      b=1;
      while(PD[b][1]!=FIN)
	{
	  for(c=1;c<=length;c++)
	    Found[c]=PD[b][c];
	  Prob += Compute_Found();
	  b++;
	}
    }
  return Prob;
}

/* obtain all minimal cuts from mcset[0] to mcset[no_mcset -1] */

void Cutset_Evaluate()
{
  int i,j,k;
  int rest;

  PATH temp1, temp2, temp3;
  void Free_Cut_List();

  {/* evaluate cutsets between mcset[i] and mcset[i+1] i = 0, 2,... */

    struct list_cuts *head, *tmp;
    int index;
    
    for(i=0; i< no_mcset; i=i+2)
      {
	index = i/2;
	head = cuts[index] = NULL;

	if((i+1)>=no_mcset)
	  { /* for the last pair when no_mcset is odd */
	    /* all elements in mcset[i] are minimal cuts */
	    for(j= 0; j< length; j++)
	      {
		if(Check_Bit(&mcset[i], j)==1)
		  {
		    tmp = (struct list_cuts *)malloc(sizeof(struct list_cuts));
		    tmp->cut = 0;
		    Set_Bit(&(tmp->cut),j);
		    tmp->next = NULL;
		    
		    if(head == NULL)
		      head = cuts[index] = tmp;
		    else
		      {
			head->next = tmp;
			head = head->next;
		      }
		  }
	      }
	  }
	else
	  {   /* mcset[i] and mcset[i+1] */
	    temp1 = mcset[i] & mcset[i+1];
	    
	    /* all elements in temp1 are minimal cuts */
	    for(j= 0; j< length; j++)
	      {
		if(Check_Bit(&temp1, j)==1)
		  {
		    tmp = (struct list_cuts *)malloc(sizeof(struct list_cuts));
		    tmp->cut = 0;
		    Set_Bit(&(tmp->cut),j);
		    tmp->next = NULL;
		    
		    if(head == NULL)
		      head = cuts[index] = tmp;
		    else
		      {
			head->next = tmp;
			head = head->next;
		      }
		  }
	      }

	    temp2 = mcset[i] & (~temp1);
	    temp3 = mcset[i+1] & (~temp1);


	    /* all combination of elements in temp2 and temp3
	       are minimal cuts */
	    for(j=0; j<length; j++)
	      if(Check_Bit(&temp2, j)==1)
		{
		  for(k=0;k<length;k++)
		    if(Check_Bit(&temp3, k)==1)
		      {
			tmp = (struct list_cuts *)
			  malloc(sizeof(struct list_cuts));
			tmp->cut = 0;
			Set_Bit(&(tmp->cut),j);
			Set_Bit(&(tmp->cut),k);
			tmp->next = NULL;
			
			if(head == NULL)
			  head = cuts[index] = tmp;
			else
			  {
			    head->next = tmp;
			    head = head->next;
			  }
		      }
		}
	  }
      }

    rest = (no_mcset +1)/2;

  }/* end of the first step */

  {/* combine cutsets between cuts[i] and cuts[i+1], i = 0, 2,...,(rest-1)*/
    /* store cuts[index] */

    struct list_cuts *head, *root, *prev, *trace1, *trace2, *tmp;

    while(rest > 1)
      {
	int index ;

	index = 0;
	for(i=0; i< rest; i=i+2)
	  {
	    if((i+1)>=rest)
	       /* for the last pair when no_mcset is odd */
	       /* all elements in cuts[i] are minimal cuts */
	      cuts[index] = cuts[i];
	    else
	      {
		/* combine cuts[i] and cuts[i+1] 
		   and store the result first in root and then in cuts[index] 
		   */
		trace1 = cuts[i]; trace2 = cuts[i+1];
		if(trace1 == NULL)
		  {
		    cuts[index] = cuts[i+1];
		    Free_Cut_List(cuts[i+1]);
		  }
		else
		  if(trace2 == NULL)
		    {
		      cuts[index] = cuts[i];
		      Free_Cut_List(cuts[i]);
		    }

		root = NULL;
		if((trace1 !=NULL)&&(trace2 != NULL))
		  {
		    while(trace1 != NULL)
		      {
			trace2 = cuts[i+1];
			while(trace2 != NULL)
			  {
			    tmp = (struct list_cuts *)
			      malloc(sizeof(struct list_cuts));
			    tmp->cut = 
			      trace1->cut | trace2->cut  ;
			    tmp->next = NULL;

			    if(root == NULL) /* first one */
			      root = tmp;    /* append */
			    else
			      { /* check tmp is a superset */
				int superset;
				
				head = root; superset = 0;
				while(head != NULL)
				  {
				    temp1 = 
				      head->cut & tmp->cut;
				    if(temp1 == head->cut)
				      {superset =1; break;}
				    head = head->next;
				  }
				if(superset == 1)
				    free(tmp);
				else
				  {
				    /* check others are tmp's superset */
				    head = prev = root;
				    while(head != NULL)
				      {
					temp1 = head->cut & tmp->cut;
					if(temp1 == tmp->cut)
					  {/* remove head */
					    if(root==head)
					      {
						root = head->next;
						free(head);
						head = prev = root;
					      }
					    else
					      {
						prev->next = head->next;
						free(head);
						head = prev->next;
					      }
					  }
					else
					  {
					    prev = head;
					    head = head->next;
					  }
				      }
				    /* append tmp */
				    if(prev != NULL)
				      prev->next = tmp;
				    else
				      root = tmp;
				  }
			      }
			    trace2 = trace2->next;
			  }
			trace1 = trace1->next;
		      }
		    Free_Cut_List(cuts[i]);
		    Free_Cut_List(cuts[i+1]);
		    cuts[index] = root;
		  }
	      } /* end of combining cuts[i] and cuts[i+1] */
	    index++;
	  }
	rest = (rest+1)/2;
      }
  }/* all min cuts are stored in cuts[0] */

  { 
    struct list_cuts *head, *prev;

    no_cuts = 0;
    head = prev = cuts[0];
    while(head != NULL)
      {
	mcut[no_cuts] = head->cut;
	head = head->next;
	free(prev);
	prev = head;

	no_cuts++;
      }
  }
}

void Free_Cut_List(struct list_cuts *cl)
{
  struct list_cuts *head, *prev;

  head = prev = cl;

  while(head!=NULL)
    {
      head = head->next;
      free(prev);
      prev = head;
    }
}

void Set_Bit(PATH *tr, int bit)
{
  bit = bit % MAX_LENGTH;
  *tr = *tr | ((unsigned long long int)1 << bit);
}

void Reset_Bit(PATH *tr, int bit)
{
  bit = bit % MAX_LENGTH;
  *tr = *tr & (~((unsigned long long int)1 << bit));
}

int Check_Bit(PATH *tr, int bit)
{
  bit = bit % MAX_LENGTH;;
  if((*tr & ((unsigned long long int)1 << bit))>0)
    return 1;
  else
    return 0;
}

double Prob_Up_Path(PATH *tr)
{
  int i;
  double prob = 1;

  for(i=0;i<length;i++)
    if((*tr &  (unsigned long long int)1 << i ? 1 : 0)==1)
      prob = prob * reliab[i];
  
  return prob;
}

double Job(int iteration)
{

  int flag; /* 0 -> Step 6, 1 -> Step 7 */
  int j, k;

  if (iteration == 0)
    {
      double tmp;

      tmp  = Prob_Up_Path(&trees[0]);
      return tmp;
    }
  else {
    /* Step 4: Null */
    
    /* Step 5: Determine Minimal Conditional Sets */
    
    for (j=0; j< iteration; j++)
      {
	mcset[j] = 0;
	mcset[j] = trees[j] & (~trees[iteration]);
	  
	/* eliminate all absorbable sets */
	for(k=0; k<j; k++)
	  {
	    PATH temp; /* no treatment for null */
	      
	    if(mcset[k] !=0)
	      {
		temp = mcset[k] & mcset[j];
		if(temp == mcset[k])
		  {
		    mcset[j] =0;
		    break;
		  }
		if(temp == mcset[j])
		  mcset[k] = 0;
	      }	      
	  }
      }

      /* stuff mcset */
    {
	int i,tmp;
	tmp = 0;
	no_mcset = 0;
	
	for(i=0; i<iteration; i++)
	  {
	    if(mcset[i] != 0)
	      {
		no_mcset++;
		if(tmp != i)
		  mcset[tmp] = mcset[i];
		tmp++;
	      }
	  }
    } 

      /* Step 6: if all mcset's are disjoint */
      {
	PATH tmp_or;

	flag = 0;
	if(no_mcset == 0)
	  {fprintf(stderr,"Error\n"); exit(-1);}

	tmp_or = mcset[0];

	for(k=1; k < no_mcset; k++)
	  {
	    if((tmp_or & mcset[k])!=0)
	      {
		flag = 1; break;
	      }
	    tmp_or = tmp_or |  mcset[k];
	  }
	
	if(flag == 0)
	  {
	    double tmp;
	    tmp  = Prob_Up_Path(&trees[iteration]);
	    for(k=0; k < no_mcset; k++)
	      tmp = tmp * (1-Prob_Up_Path(&mcset[k]));

	    return tmp;
	  }


      } /* Step 6 */


      /* Step 7: Evaluate cutset and call CDP */
      if (flag != 0)
	{
	  double tmp1, tmp2;
	  tmp1  = Prob_Up_Path(&trees[iteration]);

	  Cutset_Evaluate();

	  tmp2 = Disjoint_Procedure();
	  return (tmp1*tmp2);
	}
  } /* iteration != 0 */

  fprintf(stderr, "Reached the end of function Job.\nSomething went wrong.\n");
  exit(1);
} 

int main(void)
{
  int i, j, tmp;
  int iteration;
  double Disjoint_Procedure(), Job();
  double result;

  assert(sizeof(unsigned long long int) * BYTESIZE == MAX_LENGTH);

  scanf("%d %d", &length, &number);

  /* Step 1: Data Input */

  for(i=0; i < number; i++)  /* trees : ascending ordered of size */
    /* if they are sorted in descending order, change the above condition
       to  (i=number-1; i >= 0; i--) */
    {
      trees[i] = 0;

      for(j=0; j<length; j++)
	{
	  scanf("%d", &tmp);

	  if(tmp == 1)
	    Set_Bit(&trees[i], j);
	  else
	    Reset_Bit(&trees[i], j);
	}      
    }

  /* Read Reliabilities */
  for(j=0; j<length; j++)
    scanf("%lf", &reliab[j]);

  /* Step 2: Initialization */
  result = 0;

  /* Step 3: Updating Step */
  for(iteration = 0; iteration < number; iteration++)
    result += Job(iteration);

  printf("Probability %1.10f\n",result);
  return 0;
}
