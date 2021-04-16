/*
Fatoracao LU (ver lu.h)
Version 1.1 de 04/01/95 - Incluidos testes para eliminar mult. por zero.
*/


#include "lu.h"
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

static short eq,fases;
double Ires,deta,detb;   /*Determinante*/
double **Y1,**Y2,**E1,**E2,**A1,**A2; /*Matriz e excitacoes normal e adjunta*/
double Rmult(double x1,double x2,double y1,double y2);
double Rdiv(double x1,double x2,double y1,double y2);

double Rmult(double x1,double x2,double y1,double y2)
{
  if (((x1==0)&&(x2==0))||((y1==0)&&(y2==0))) {
    Ires=0;
    return 0;
  }
  else {
    Ires=x1*y2+x2*y1;
    return (x1*y1-x2*y2);
  }
}

double Rdiv(double x1,double x2,double y1,double y2)
{
  double Result;
  double t;

  t=y1*y1+y2*y2;
  Result=Rmult(x1,x2,y1,-y2)/t;
  Ires/=t;
  return Result;
}

boolean AlocarMatriz(double ***p,short linhas,short colunas)
{
  short i,j,tcoluna,tlinha;

  tcoluna=(linhas+1)*sizeof(void*);
  tlinha=(colunas+1)*sizeof(double);
  if ((*p=(double**)malloc(tcoluna))!=0) {
      for (i=0; i<=linhas; i++) {
	  if (((*p)[i]=(double*)malloc(tlinha))==0) {
	      for (j=i-1; j>=0; j--) {
		  free((char*)(*p)[j]);
	      }
	      free((char*)(*p));
	      *p=NULL;
	      return false;
	  }
      }
      return true;
  }
  else
    return false;
}

void DesalocarMatriz(double ***p,short linhas,short colunas)
{
  short i;

  for (i=linhas; i>=0; i--) free((char*)((*p)[i]));
  free((char*)(*p));
  *p=NULL;
}

boolean AlocarSistema(short neq,short nfases)
{
  eq=neq;
  fases=nfases;
  return(AlocarMatriz(&Y1,eq,eq)&&AlocarMatriz(&Y2,eq,eq)&&
	 AlocarMatriz(&E1,eq,fases)&&AlocarMatriz(&E2,eq,fases)&&
	 AlocarMatriz(&A1,eq,fases)&&AlocarMatriz(&A2,eq,fases));
}

void DesalocarSistema(void)
{
  DesalocarMatriz(&Y1,eq,eq);
  DesalocarMatriz(&Y2,eq,eq);
  DesalocarMatriz(&E1,eq,fases);
  DesalocarMatriz(&E2,eq,fases);
  DesalocarMatriz(&A1,eq,fases);
  DesalocarMatriz(&A2,eq,fases);
}

boolean ResolverSistema(short *Ax,double dmin)
{
  short i,j,k,ii;
  double t1,t2,d1,d2;
  double *t;

  /*Fatoracao LU*/
  deta=1.0;
  detb=0.0;
  for (i=1; i<eq; i++) {
      ii=i+1;
      t1=Y1[i][i];
      t2=Y2[i][i];
      /*Condensacao pivotal*/
      k=i;
      for (j=ii; j<=eq; j++) {
	  if (fabs(Y1[j][i])+fabs(Y2[j][i])>fabs(t1)+fabs(t2)) {
	      t1=Y1[j][i];
	      t2=Y2[j][i];
	      k=j;
	  }
      }
      if (k!=i) {
	  deta=-deta;
	  detb=-detb;
	  /*Trocando os pointers:*/
	  t=Y1[i];
	  Y1[i]=Y1[k];
	  Y1[k]=t;
	  t=Y2[i];
	  Y2[i]=Y2[k];
	  Y2[k]=t;
	  t=E1[i];
	  E1[i]=E1[k];
	  E1[k]=t;
	  t=E2[i];
	  E2[i]=E2[k];
	  E2[k]=t;
	  for (j=1; j<=eq; j++) {
	      if (Ax[j]==i)
		Ax[j]=k;
	      else if (Ax[j]==k)
		Ax[j]=i;
	  }
      }
      /*Pivot muito pequeno*/
      if (fabs(t1)+fabs(t2)<dmin)
	return false;
      for (j=ii; j<=eq; j++) {
	  Y1[i][j]=Rdiv(Y1[i][j],Y2[i][j],t1,t2);
	  Y2[i][j]=Ires;
      }
      for (j=ii; j<=eq; j++) {
	  t1=Y1[j][i];
	  t2=Y2[j][i];
          if ((t1!=0)||(t2!=0))
	    for (k=ii; k<=eq; k++) {
	      Y1[j][k]-=Rmult(t1,t2,Y1[i][k],Y2[i][k]);
	      Y2[j][k]-=Ires;
	  }
      }
  }
  /*Determinante*/
  for (i=1; i<=eq; i++) {
      deta=Rmult(deta,detb,Y1[i][i],Y2[i][i]);
      detb=Ires;
  }
  /*Determinante muito pequeno*/
  if (fabs(deta)+fabs(detb)<dmin)
    return false;
  /*Substituicoes*/
  for (ii=1; ii<=fases; ii++) {
      /*Substituicao direta*/
      E1[1][ii]=Rdiv(E1[1][ii],E2[1][ii],Y1[1][1],Y2[1][1]);
      E2[1][ii]=Ires;
      for (k=2; k<=eq; k++) {
	  t1=0.0;
	  t2=0.0;
	  d1=0.0;
	  d2=0.0;
	  for (j=1; j<k; j++) {
	      t1+=Rmult(Y1[k][j],Y2[k][j],E1[j][ii],E2[j][ii]);
	      t2+=Ires;
	      d1+=Rmult(Y1[j][k],Y2[j][k],A1[j][ii],A2[j][ii]);
	      d2+=Ires;
	  }
	  E1[k][ii]=Rdiv(E1[k][ii]-t1,E2[k][ii]-t2,Y1[k][k],Y2[k][k]);
	  E2[k][ii]=Ires;
	  A1[k][ii]-=d1;
	  A2[k][ii]-=d2;
      }
      /*Substituicao reversa*/
      A1[eq][ii]=Rdiv(A1[eq][ii],A2[eq][ii],Y1[eq][eq],Y2[eq][eq]);
      A2[eq][ii]=Ires;
      for (k=eq-1; k>=1; k--) {
	  t1=0.0;
	  t2=0.0;
	  d1=0.0;
	  d2=0.0;
	  for (j=k+1; j<=eq; j++) {
	      t1+=Rmult(Y1[k][j],Y2[k][j],E1[j][ii],E2[j][ii]);
	      t2+=Ires;
	      d1+=Rmult(Y1[j][k],Y2[j][k],A1[j][ii],A2[j][ii]);
	      d2+=Ires;
	  }
	  A1[k][ii]=Rdiv(A1[k][ii]-d1,A2[k][ii]-d2,Y1[k][k],Y2[k][k]);
	  A2[k][ii]=Ires;
	  E1[k][ii]-=t1;
	  E2[k][ii]-=t2;
      }
  }
  return true;
}  /*ResolverSistema*/

/* End */
