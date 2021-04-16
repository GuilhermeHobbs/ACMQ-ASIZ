/*
Versao Sun XView em C do programa ASIZ
*****************************************************************************
Analise de circuitos a corrente chaveada em transformada Z - Versao XView
Antonio Carlos Moreirao de Queiroz - COPPE/DEEL-UFRJ - 1992
V. 1.0  Traducao para C da versao 1.2c em Pascal
V. 1.0  26/8/94: Introduzida variavel reffases
V. 1.0a 21/09/94: Substituida XDrawRectangle
V. 1.1  26/10/94: Calculo de espectro em implementacao
                  Arquivo para selecao separado
                  Retencao opcional do grafico de resp. freq.
                  Curvas c/erro no relatorio
V. 1.2  30/11/94: Eliminada janela de mensagens.
V. 1.2a 02/01/95: Mudados deta e detb, uso de da e db, elim. denominador
                  e raizes_validas
V. 1.2b 25/01/95: Ordem maxima=127, Mudado tratamento da VCVS
V. 1.2c 29/01/95: Alocacao otimizada dos polinomios. Normalizacao correta
V. 1.3  18/09/95: Acoplamentos diretos. Tudo parece certo. Falta conferir.
V. 1.3a 27/09/95: Atraso de grupo aproximado, Lista ganhos. Parece ok.         *****************************************************************************
*/

#define versao "1.3a of 27/09/95 (Sun)"

#include <string.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <assert.h>
#include <time.h>
#include <floatingpoint.h>
#include "lu.h"
#include <memory.h>
#include <X11/Xlib.h>
#include <xview/xview.h>
#include <xview/canvas.h>
#include <xview/xv_xrect.h>
#include <xview/cms.h>
#include <xview/textsw.h>
#include <xview/panel.h>
#include <xview/notice.h>
#include <xview/svrimage.h>
#include <xview/icon.h>
#define KTAB 9
#define KBS 8
#define KDEL 127
#define KCTRLB 2
#define KCTRLC 3
#define KCTRLK 11
#define KCTRLL 12
#define KCTRLO 15
#define KCTRLP 16
#define KCTRLQ 17
#define KCTRLR 18
#define KCTRLS 19
#define KCTRLT 20
#define KCTRLU 21
#define KCTRLV 22
#define KCTRLW 23
#define KCTRLY 25
#define KCTRLZ 26
#define KESC 27
#define KUPARROW 32596
#define KDOWNARROW 32602
#define KLEFTARROW 32598
#define KRIGHTARROW 32600
#define KF1 0
#define fftmax          128    /*Maximo grau para FFT*/
#define nosmax          500    /*Maximo numero de nos*/
#define elmax           4000   /*Numero maximo de elementos, exclusive chaves*/
#define graumax         (fftmax-1)   /*Grau maximo dos polinomios em z*/
#define grandemax       (fftmax*fasmax-1)   /*Idem, dos polinomios em z^1/fases*/
#define cm              15   /*Campo numerico real*/
#define dc              9    /*Decimais de real*/
#define tamnome         5    /*Tamanho dos nomes dos elementos*/
#define intnome         (tamnome+3)   /*Tamanho dos nomes internos*/
#define sg              ".sgr"
#define tmargin         20
#define txth            14

/* defines para substituir xv_get e xv_set */

#define get_int(x) (int)xv_get(x,PANEL_VALUE)
#define get_real(x) atof((char*)xv_get(x,PANEL_VALUE))
#define get_text(x) (char*)xv_get(x,PANEL_VALUE)
#define get_dx(x) (int)xv_get(x,XV_WIDTH)
#define get_dy(x) (int)xv_get(x,XV_HEIGHT)
#define get_sel(x) (int)xv_get(x,PANEL_VALUE)
#define get_item(x) (int)xv_get(sel_menu,MENU_VALUE)-1
char buf[20];
#define set_int(x,y) xv_set(x,PANEL_VALUE,y,NULL)
#define set_real(x,y) xv_set(x,PANEL_VALUE,gcvt(y,15,buf),NULL)
#define set_sel(x,y) xv_set(x,PANEL_VALUE,y,NULL)
#define set_max(x,y) xv_set(x,PANEL_MAX_VALUE,y,NULL)
#define close_window(w) xv_set(w,XV_SHOW,FALSE,NULL)
#define open_window(w) xv_set(w,XV_SHOW,TRUE,NULL)
#define xv_ok 1

/* defines para os headers das funcoes callback */

#define notify_button(xxx) void xxx(Panel_item obj, Event* event)
#define notify_textfield(xxx) Panel_setting xxx(Panel_item obj, Event *event)
#define notify_setting(xxx) void xxx(Panel_item obj, int sel_setting, Event* event)
#define notify_menu(xxx) void xxx(Menu obj, Menu_item sel_menu)
#define event_canvas(xxx) void xxx(Xv_window window, Event *event)
#define notify_canvas(xxx) void xxx(Canvas obj, Xv_Window paint_window, Display* dpy, Window xwin, Xv_xrectlist* xrects)

int evento;
Cms cms;
GC Ggc,Fgc,Tgc,Rgc,Sgc;
unsigned long c_cursor;
/*!!! Porque da erro declarar tudo junto? */
Display* Gdisplay;
Display* Fdisplay;
Display* Tdisplay;
Display* Rdisplay;
Display* Sdisplay;
Window Gxid,Fxid,Txid,Rxid,Sxid;
int Fpronto=0,Tpronto=0,Rpronto=0,Spronto=0;
short closed_bits[]= {
#include "asiz.icon"
};
Server_image closed_image;
Icon icon;

typedef enum {
  resistor,chave,fonteI,fonteV,capacitor,amplificador,VCCS,VCVS
} elemento;
typedef double coefgrande[grandemax+1];

typedef struct polpequeno {
  double *cre, *cim;
  short g,minpot;
  double vala,valb;
  boolean valido;
} polpequeno;

typedef struct polgrande {
  coefgrande cf;
  short g;
} polgrande;

typedef struct raizes {
  double re[grandemax],im[grandemax];
  short g;
  boolean calculados;
} raizes;

typedef short apontadores[fasmax][nosmax+1];
typedef polpequeno numfases[fasmax];
typedef polpequeno *numeradores[linmax];
typedef boolean identificador[linmax+1];
typedef enum {
  frequencia,transiente
} tipotabela;

typedef struct _REC_NetList {
  char nome[intnome+1];
  short n1,n2;
  boolean selecionado;
  char grupo;
  elemento tipo;
  union {
    double Res;
    double Is;
    struct {
      short nox;
      double Vs;
    } U3;
    short fase;
    double Cap;
    short nout;
    struct {
      short n3,n4;
      double Gm;
    } U6;
    struct {
      short noxc,n3c,n4c;
      double Av;
    } U7;
  } UU;
} _REC_NetList;

/*Variaveis dos graficos*/

#define refmax          4
#define segmax          2000
#define xmin            60
#define ymin            30

typedef double grafico[segmax+1];

typedef struct tiporeffreq {
  polgrande Rnglobal;     /*Numerador da referencia*/
  polpequeno Rden;        /*Denominador da referencia*/
  boolean reffreqreter;   /*S/H na referencia*/
  short reffases;         /*Numero de fases*/
  grafico Rgan;           /*Modulo e fase da referencia*/
  grafico Rang;
  grafico RTg;            /*Tg*/
} tiporeffreq;

typedef struct tiporeftran {
  short ultimotran;       /*Ultimo ponto da referencia transiente*/
  grafico RTempo, RVo;    /*Tempo e tensao*/
} tiporeftran;

char grupoatual='*';
/*Estado do programa*/
boolean netlist_valido=false,analise_valida=false,
	       polos_validos=false,zeros_validos=false,
	       frequencia_valida=false,desvios_validos=false,
	       transiente_valido=false,
               reter_imagem=false;
/*Interface*/
Xv_opaque menu1,menuf,menut,menur,jfrequencia,
		 cfrequencia,jraizes,craizes,jtransiente,ctransiente,
		 jnetlist,tnetlist,tfases,bread,jpanalise,tnsaida,
		 traio,tdisp,tminimo,tgrau,ssh,tfs,banalisar,jpraizes,
		 ttolz,ttolp,treal,timag,tremin,timmin,tdelta,bplot,
		 blist,jpfrequencia,twmin,twmax,tgmin,tgmax,ttgmin,ttgmax,slog,
		 srads,tsegmf,brf,jptransiente,stinput,brt,tfase,
		 tfreq,tampl,tsegi,sinput,tsegmt,tvmax,tvmin,jsensi,ssensi,
		 sdesvios,tvar,brsensi,bwsensi,csensi,jpnumerador,
		 tsaida,stiponum,tfk,tfj,sadjunto,blistnum,jrelatorio,
		 trelatorio,brelatorio,
                 /*jdiretorio,cdiretorio,tmask,*/
                 jmos,scap,tcgs,tcgd,sgds,tgds,panel,ganalise,
                 jpespectro,tsp,bpsp,blsp;

short placa,modo;       /*Modo grafico*/
short i,j,k;            /*Uso geral*/
long mm;                /*Usado para medicoes de memoria*/
boolean ok;
char txt[256];
char ch;
short nos,elementos,fases;   /*Dimensoes do circuito*/
short fasesatual;            /*Fases do circuito atual*/
short variaveis;             /*Numero de variaveis calculadas*/
double z1f,z2f,z1,z2;        /*z^(1/f), z*/
double w;                    /*frequencia atual em rads/s*/
short equacoes;              /*Equacoes no sistema final*/
short e;                     /*Contador de elementos*/
short jmin,jmax,kmin,kmax;   /*Limites das fases no numerador*/
char rede[256];              /*Nome da rede*/
FILE *arquivo;               /*E/S*/
short graufft;               /*Grau da FFT*/
short ordemfft;              /*Ordem da FFT*/
double Ncte;                 /*Cte multiplicativa do denominador*/
short capacitivas;           /*Numero de equacoes capacitivas*/
polpequeno Nden;             /*Denominador*/
numeradores Npa;             /*Numeradores da rede normal*/
numeradores Apa;             /*Numeradores da rede adjunta*/
polgrande Nglobal;           /*Numerador global*/
short reffreq;               /*Numero de referencias na resposta em frequencia*/
short reftran;               /*Numero de referencia na resposta transiente*/
boolean relatorio;           /*Se existe relatorio aberto*/
boolean plotarfase;          /*Se a fase deve ser plotada*/
boolean plotaratraso;        /*Se o Tg deve ser plotado*/
short maxz;                  /*Maxima potencia de z^1/f*/
short npl;                   /*Nomes por linha na janela de p. sensibilidade*/
raizes Polos,Zeros;          /*Polos e zeros*/
apontadores C,L;             /*Apontador de colunas/linhas*/
identificador Eqcap;         /*Se as equacoes/linhas sao capacitivas*/
boolean normal;              /*Modo de inclusao de Ggs e capacitores*/
tipotabela asalvar;          /*O que deve ser salvo no relatorio*/
short total,nomes;           /*Usado na selecao de arquivo*/
_REC_NetList NetList[elmax];
short ioresult;
unsigned int sizepoly=0, sizenum=0; /*Tamanhos dos polinomios*/
short fasesantes, equacoesantes;; /*Dados da ultima analise feita*/

char unid[2][5]={
  "rd/s","Hz"
};

boolean grade=true;

typedef unsigned long* cores;
#define TCOR unsigned long
cores cor;

/*Resposta em Frequencia*/
double *Frq,*Gan,*Ang,*Tg,*Dgan,*Dang; /*Valores do grafico*/
tiporeffreq *Reff[refmax];         /*Referencia*/
short yfmax,xfmax;                 /*Limites*/
short ultimof,hf;                  /*Ultimo ponto e ponto atual*/
short fcsr,colcsr;                 /*Cursor*/
double ah,bh,aw,bw,ag,bg,af,bf;    /*Mapeamento*/
double ad,bd;                      /*Mapeamento do Tg*/
boolean plotardesvios;             /*Calcular desvios*/
/*Polos e zeros*/
double ay,by,ax,bx;                /*Mapeamento*/
short rcsr,xcursor,ycursor;        /*Cursor*/
short xrmax,yrmax;                 /*Limites*/
/*Resposta transiente*/
double *Tempo,*Vi,*Vo;             /*Valores nos graficos*/
tiporeftran *Reft[refmax];         /*Referencia*/
short xtmax,ytmax;                 /*Limites*/
short ultimot,ht;                  /*Ultimo ponto e ponto atual*/
short ppf;                         /*Pontos por fase*/
double av,bv,at,bt;                /*Mapeamento*/
short tcsr,ctcsr;                  /*Cursor*/

/* Versao alternativa para XDrawRectangle */

void quadrado(int x,int y,int dx,int dy)
{
  XDrawLine(Gdisplay,Gxid,Ggc,x,y,x+dx,y);
  XDrawLine(Gdisplay,Gxid,Ggc,x+dx,y,x+dx,y+dy);
  XDrawLine(Gdisplay,Gxid,Ggc,x+dx,y+dy,x,y+dy);
  XDrawLine(Gdisplay,Gxid,Ggc,x,y+dy,x,y);
}

#define XDrawRectangle(gd,gx,gg,x,y,dx,dy) quadrado(x,y,dx,dy)

short pos(char c, char* str2)
{
   char* res;
   res=strchr(str2,c);
   if (res==NULL) return 0;
   else return res-str2+1;
}

double Ex(double x,double t)
{
  return exp(t*log(x));
}

boolean AnaliseValida(void)
{
  boolean Result;

  Result=analise_valida;
  if (!analise_valida) puts("* No circuit was analyzed");
  return Result;
}

boolean Estatistico(void)
{
  return(get_sel(sdesvios)==0);
}

boolean Adjunto(void)
{
  return(get_sel(sadjunto)==1);
}

boolean Log(void)
{
  return(get_sel(slog)==0);
}

boolean Hertz(void)
{
  return(get_sel(srads)==1);
}

void ModuloFase(double ta, double tb, double *mdl, double *fas)
{
  *mdl=log(ta*ta+tb*tb)*4.342944819;
  *fas=atan(tb/ta)*57.29577951;
  if (ta<0)
    if (tb>0) *fas=180+*fas; else *fas=*fas-180;
}

void ErroFatal(char *texto)
{
   notice_prompt(jfrequencia,NULL,
      NOTICE_MESSAGE_STRINGS,"Error",texto,"ASIZ will quit",NULL,
      NOTICE_BUTTON,"Ok",1000,
    NULL);
  if (relatorio) fclose(arquivo);
  puts("ASIZ interrupted");
  exit(1);
}

char *NomeAtual(char *Result)
{
   sprintf(txt,"N(%hd",get_int(tsaida));
   if (get_sel(stiponum)==0)
     sprintf(txt+strlen(txt),",%hd,%hd",
	get_int(tfk),
	get_int(tfj));
   strcat(txt,")");
   if (Adjunto())
     strcat(txt,"^");
   if (get_int(tsaida)>nos)
     strcat(txt,"(aux)");
   return strcpy(Result,txt);
}

/* variables for AnalisarNoCirculo: */
struct LOC_AnalisarNoCirculo {
  double w;   /*Angulo atual de Z*/
  double t;   /*Expoentes*/
  double r;   /*Exponenciais do raio*/
  short x;    /*Ponto atual no circulo*/
  short conj; /*Ponto complexo conjugado*/
} ;

/* variables for MontarSistema: */
struct LOC_MontarSistema {
  struct LOC_AnalisarNoCirculo *LINK;
  short l1,l2,c1,c2;
} ;

void Transcondutancia(short na,short nb,short nc,short nd,short f1,
			    short f2,double g1,double g2,
			    struct LOC_MontarSistema *LINK)
{
  LINK->l1=L[f1-1][na];
  LINK->l2=L[f1-1][nb];
  LINK->c1=C[f2-1][nc];
  LINK->c2=C[f2-1][nd];
  if (normal||Eqcap[LINK->l1]) {
      Y1[LINK->l1][LINK->c1]+=g1;
      Y1[LINK->l1][LINK->c2]-=g1;
      Y2[LINK->l1][LINK->c1]+=g2;
      Y2[LINK->l1][LINK->c2]-=g2;
  }
  if (!(normal||Eqcap[LINK->l2]))
    return;
  Y1[LINK->l2][LINK->c2]+=g1;
  Y1[LINK->l2][LINK->c1]-=g1;
  Y2[LINK->l2][LINK->c2]+=g2;
  Y2[LINK->l2][LINK->c1]-=g2;
}

void MontarSistema(struct LOC_AnalisarNoCirculo *LINK)
{
  struct LOC_MontarSistema V;
  _REC_NetList *WITH;
  double t;

  V.LINK=LINK;
  for (i=0; i<=equacoes; i++) {
      for (j=0; j<=equacoes; j++) {
	  Y1[i][j]=0.0;
	  Y2[i][j]=0.0;
      }
      for (j=1; j<=fases; j++) {
	  E1[i][j]=0.0;
	  E2[i][j]=0.0;
	  A1[i][j]=0.0;
	  A2[i][j]=0.0;
      }
  }
  for (i=1; i<=fases; i++) {
      A1[C[i-1][get_int(tnsaida)]][i]=-z1f;
      A2[C[i-1][get_int(tnsaida)]][i]=-z2f;
  }
  for (e=1; e<=elementos; e++) {
      WITH=&NetList[e-1];
      switch (WITH->tipo) {

	case fonteV:
	  for (i=1; i<=fases; i++) {
	      V.l1=L[i-1][WITH->UU.U3.nox];
	      E1[V.l1][i]-=WITH->UU.U3.Vs;
	      Y1[V.l1][C[i-1][WITH->n1]]-=1;
	      Y1[V.l1][C[i-1][WITH->n2]]+=1;
	  }
	  break;

	case VCVS:
          t=1/WITH->UU.U7.Av;
	  for (i=1; i<=fases; i++) {
	      V.l1=L[i-1][WITH->UU.U7.noxc];
	      Y1[V.l1][C[i-1][WITH->n1]]-=t;
	      Y1[V.l1][C[i-1][WITH->n2]]+=t;
              Y1[V.l1][C[i-1][WITH->UU.U7.n3c]]+=1;
              Y1[V.l1][C[i-1][WITH->UU.U7.n4c]]-=1;
          }
          break;

        case VCCS:
          for (i=1; i<=fases; i++)
            Transcondutancia(WITH->n1,WITH->n2,WITH->UU.U6.n3,WITH->UU.U6.n4,
                             i,i,WITH->UU.U6.Gm,0.0,&V);
          break;

        case resistor:
          for (i=1; i<=fases; i++)
            Transcondutancia(WITH->n1,WITH->n2,WITH->n1,WITH->n2,i,i,
                             1/WITH->UU.Res,0.0,&V);
          break;

        case capacitor:
          for (i=1; i<=fases; i++) {
              normal=false;
              /*Os termos abaixo so devem entrar em eqs. capacitivas*/
              /*O primeiro e sempre multiplicado por z*/
              /*e o segundo nunca*/
              Transcondutancia(WITH->n1,WITH->n2,WITH->n1,WITH->n2,i,i,
                               WITH->UU.Cap*z1f,WITH->UU.Cap*z2f,&V);
	      Transcondutancia(WITH->n1,WITH->n2,WITH->n1,WITH->n2,i%fases+1,
                               i,-WITH->UU.Cap,0.0,&V);
              normal=true;
          }
          break;

        case fonteI:
	  for (i=1; i<=fases; i++) {
              V.l1=L[i-1][WITH->n1];
              V.l2=L[i-1][WITH->n2];
              E1[V.l1][i]-=WITH->UU.Is;
              E1[V.l2][i]+=WITH->UU.Is;
          }
          break;

        default:
          ErroFatal("Something is wrong");
          break;
      }
  }
}  /*MontarSistema*/

void GuardarDenominador(struct LOC_AnalisarNoCirculo *LINK)
{
  double DUMMY;

  /*Correcao para o denominador*/
  LINK->t=modf((double)maxz/fases,&DUMMY);
  if (LINK->t!=0) {
      LINK->t=1-LINK->t;
      LINK->r=Ex(get_real(traio),LINK->t);
      deta=Rmult(deta,detb,LINK->r*cos(LINK->w*LINK->t),
                 LINK->r*sin(LINK->w*LINK->t));
      detb=Ires;
  }
  LINK->conj=(graufft-LINK->x)%graufft;
  Nden.cre[LINK->x]=deta;
  Nden.cim[LINK->x]=detb;
  Nden.cre[LINK->conj]=deta;
  Nden.cim[LINK->conj]=-detb;
  Nden.minpot=0;
}

void GuardarNumeradores(double **S1,double **S2,polpequeno **Num,
                              short (*Q)[nosmax+1],short *Qx,boolean adjunto,
                              struct LOC_AnalisarNoCirculo *LINK)
{
  short f;
  double na,nb;
  polpequeno *WITH;

  for (i=1; i<=equacoes; i++) {
      for (j=1; j<=fases; j++) {
          na=Rmult(S1[Qx[i]][j],S2[Qx[i]][j],deta,detb);
          nb=Ires;
          /*Correcao para os numeradores*/
          /*E necessario descobrir a que fase f i pertence*/
          /*Isto poderia ser feito uma so vez*/
          f=0;
          do {
              f++;
              k=0;
              do {
                  k++;
                  ok=(k<=variaveis&&Q[f-1][k]==i);
              } while (!(ok||k>variaveis));
          } while (!ok);
          if (adjunto) {
              k=-((f-j+fases)%fases);   /*Importante detalhe*/
	  }
	  else {
	      k=-((j-f+fases)%fases);
	  }
          if (f!=j) {
	      LINK->t=(double)k/fases;
	      LINK->r=Ex(get_real(traio),LINK->t);
              na=Rmult(na,nb,LINK->r*cos(LINK->w*LINK->t),
                         LINK->r*sin(LINK->w*LINK->t));
              nb=Ires;
          }
          /*Correcao para numeradores do sistema adjunto
            em linhas nao capacitivas, nao multiplicadas*/
          if (adjunto&&!Eqcap[i]) {
              na=Rdiv(na,nb,z1f,z2f);
              nb=Ires;
          }
          WITH=&Num[i-1][j-1];
          WITH->cre[LINK->x]=na;
          WITH->cim[LINK->x]=nb;
          WITH->cre[LINK->conj]=na;
          WITH->cim[LINK->conj]=-nb;
          WITH->minpot=-k;
      }
  }
}  /*GuardarNumeradores*/

void NaoDa(void) {
  ErroFatal("Not enough memory");
}

void AnalisarNoCirculo(void)
{
  struct LOC_AnalisarNoCirculo V;
  indice Ax,Nx;   /*Para lembrar onde estao as variaveis*/
  short FORLIM;
  char STR2[256];

  for (i=0; i<=equacoes; i++)
    Nx[i]=i;
  graufft=1;
  ordemfft=0;
  while (graufft<=get_int(tgrau)) {
      graufft*=2;
      ordemfft++;
  }
  sprintf(STR2,"Interpolation degree (in z): %hd",graufft);
  puts(STR2);
  if (graufft>fftmax) {
      sprintf(STR2,"The maximum degree is %hd",graumax);
      ErroFatal(STR2);
  }
  /*Realocacao das tensoes nodais*/
  if (sizenum!=0) {
    for (i=equacoesantes-1; i>=0; i--) {
      for (j=fasesantes-1; j>=0; j--) {
	free((char*)Apa[i][j].cim);
	free((char*)Apa[i][j].cre);
	free((char*)Npa[i][j].cim);
	free((char*)Npa[i][j].cre);
      }
      free((char*)Apa[i]);
      free((char*)Npa[i]);
    }
    free((char*)Nden.cim);
    free((char*)Nden.cre);
  }
  sizepoly=(graufft+1)*sizeof(double);
  sizenum=fases*sizeof(polpequeno);
  fasesantes=fases;
  equacoesantes=equacoes;
  if ((Nden.cre=(double*)malloc(sizepoly))==0)  NaoDa();
  if ((Nden.cim=(double*)malloc(sizepoly))==0)  NaoDa();
  for (i=0; i<equacoes; i++) {
    if ((Npa[i]=(polpequeno*)malloc(sizenum))==0) NaoDa();
    if ((Apa[i]=(polpequeno*)malloc(sizenum))==0) NaoDa();
    for (j=0; j<fases; j++) {
      if ((Npa[i][j].cre=(double*)malloc(sizepoly))==0) NaoDa();
      if ((Npa[i][j].cim=(double*)malloc(sizepoly))==0) NaoDa();
      if ((Apa[i][j].cre=(double*)malloc(sizepoly))==0) NaoDa();
      if ((Apa[i][j].cim=(double*)malloc(sizepoly))==0) NaoDa();
    }
  }
  if (!AlocarSistema(equacoes,fases)) {
      ErroFatal("Not enough memory for the system of equations");
      return;
  }
  FORLIM=graufft/2;
  open_window(jpanalise);
  xv_set(ganalise,PANEL_MAX_VALUE,FORLIM,PANEL_LABEL_STRING,"Analyzing",NULL);
  for (V.x=0; V.x<=FORLIM; V.x++) {
      memcpy((char*)Ax,(char*)Nx,sizeof(indice));
      xv_set(ganalise,PANEL_VALUE,V.x,NULL);
      XFlush((Display*)xv_get(jpanalise,XV_DISPLAY));
      V.w=2*M_PI/graufft*V.x;
      V.r=Ex(get_real(traio),1.0/fases);
      z1f=V.r*cos(V.w/fases);
      z2f=V.r*sin(V.w/fases);
      MontarSistema(&V);
      if (!ResolverSistema(Ax,get_real(tminimo)))
        ErroFatal("System determinant too small. Verify if there are floating subcircuits.");
      GuardarDenominador(&V);
      GuardarNumeradores(E1,E2,Npa,C,Nx,false,&V);
      GuardarNumeradores(A1,A2,Apa,L,Ax,true,&V);
  }
  DesalocarSistema();
}  /*AnalisarNoCirculo*/

/* variables for FFT: */
struct LOC_FFT {
  short n;
} ;

short Inverso(short x,struct LOC_FFT *LINK)
{
  short i,u;

  u=0;
  i=((unsigned)LINK->n)>>1;
  do {
      if (x&1)
        u+=i;
      i=((unsigned)i)>>1;
      x=((unsigned)x)>>1;
  } while (x!=0);
  return u;
}

void FFT(double *A,double *B,short n_,short m,boolean direto)
{
  struct LOC_FFT V;
  short k,k1,l,s,i,j,i1,i2,FORLIM;
  double x1,x2,y1,y2;

  V.n=n_;
  for (k=m-1; k>=0; k--) {
      k1=1<<k;
      l=0;
      do {
          s=Inverso(l/k1,&V);
          x1=cos(2*M_PI*s/V.n);
          y1=sin(2*M_PI*s/V.n);
          if (direto)
            y1=-y1;
          for (j=0; j<k1; j++) {
              i1=j+l+k1;
              i2=j+l;
              x2=A[i1]*x1-B[i1]*y1;
              y2=A[i1]*y1+B[i1]*x1;
              A[i2]+=x2;
              B[i2]+=y2;
              A[i1]=A[i2]-x2-x2;
              B[i1]=B[i2]-y2-y2;
          }
          l+=k1<<1;
      } while (l<V.n);
  }
  FORLIM=V.n;
  for (i=0; i<FORLIM; i++) {
      s=Inverso(i,&V);
      if (s>i) {
          x1=A[i];
          A[i]=A[s];
          A[s]=x1;
          x1=B[i];
          B[i]=B[s];
          B[s]=x1;
      }
  }
  if (!direto)
    return;
  FORLIM=V.n;
  for (i=0; i<FORLIM; i++) {
      A[i]/=V.n;
      B[i]/=V.n;
  }
}  /*FFT*/

void Normalizar(polpequeno *A,double *cte,boolean denominador)
{
  double maximo;
  short i,FORLIM;

  A->g=graufft-1;
  maximo=0.0;
  FORLIM=A->g;
  for (i=1; i<=FORLIM; i++)
    A->cre[i]/=exp(i*log(get_real(traio)));
  for (i=0; i<=FORLIM; i++) {
      if (fabs(A->cre[i])>maximo)
        maximo=fabs(A->cre[i]);
  }
  maximo/=get_real(tdisp);
  for (i=0; i<=FORLIM; i++) {
      if (fabs(A->cre[i])<maximo)
        A->cre[i]=0.0;
  }
  while (A->cre[A->g]==0&&A->g>0)
    A->g--;
  if (denominador)
    *cte=A->cre[A->g];
  FORLIM=A->g;
  for (i=0; i<=FORLIM; i++)
    A->cre[i]/=*cte;
  if (fabs(A->cre[A->g])<get_real(tminimo)) {
    A->g=0;
    A->cre[0]=0.0;
  }
}

void InterpolarNumeradores(polpequeno **Num,double *cte,char *n_a)
{
  int k;

  xv_set(ganalise,PANEL_LABEL_STRING,n_a,PANEL_MAX_VALUE,equacoes*fases,PANEL_VALUE,0,NULL);
  k=0;
  for (i=1; i<=equacoes; i++) {
      for (j=1; j<=fases; j++) {
          k++;
          FFT(Num[i-1][j-1].cre,Num[i-1][j-1].cim,graufft,ordemfft,true);
          Normalizar(&Num[i-1][j-1],cte,false);
      }
      xv_set(ganalise,PANEL_VALUE,k,NULL);
      XFlush((Display*)xv_get(jpanalise,XV_DISPLAY));
  }
}

void InterpolarPolinomios(void)
{
  xv_set(ganalise,PANEL_LABEL_STRING,"Denominator",PANEL_MAX_VALUE,1,PANEL_VALUE,0,NULL);
  XFlush((Display*)xv_get(jpanalise,XV_DISPLAY));
  FFT(Nden.cre,Nden.cim,graufft,ordemfft,true);
  Normalizar(&Nden,&Ncte,true);
  printf("Condition number: %g\n",Ncte);
  InterpolarNumeradores(Npa,&Ncte,"Normal numerators");
  InterpolarNumeradores(Apa,&Ncte,"Adjoint numerators");
  xv_set(ganalise,PANEL_LABEL_STRING,"Analysis",PANEL_MAX_VALUE,100,PANEL_VALUE,100,NULL);
}

char *Expoente(char *Result,short n,short d)
{
  /*String com expoente fracion rio de z*/
  short i,f;

  i=n/d;
  f=n%d;
  if (i>0&&f>0)
    sprintf(txt,"%hd %hd/%hd",i,f,d);
  else if (i==0&&f>0)
    sprintf(txt,"%hd/%hd",f,d);
  else if (f==0)
    sprintf(txt,"%hd",i);
  else
    strcpy(txt,"0");
  while (strlen(txt)<8)
    strcat(txt," ");
  return strcpy(Result,txt);
}

void ListarPequeno(polpequeno *A)
{
  short FORLIM;
  char STR2[256];
  char STR3[256];

  FORLIM=A->g;
  for (i=0; i<=FORLIM; i++) {
      j=A->minpot+i*fases;
      sprintf(STR2,"% .10e z^(%s)",A->cre[i],Expoente(STR3,j,fases));
      puts(STR2);
  }
}

void ListarGrande(void)
{
  short FORLIM;
  char STR2[256];
  char STR3[256];

  FORLIM=Nglobal.g;
  for (i=0; i<=FORLIM; i++) {
      sprintf(STR2,"% .10e z^(%s)",Nglobal.cf[i],Expoente(STR3,i,fases));
      puts(STR2);
  }
}

void GerarGlobal(void)
{
  numeradores Num;
  short j,k,jj,kk,FORLIM2;

  if (get_sel(stiponum)==0) {
      jmin=get_int(tfj);
      jmax=jmin;
      kmin=get_int(tfk);
      kmax=kmin;
  }
  else {
      jmin=1;
      jmax=fases;
      kmin=1;
      kmax=fases;
  }
  if (Adjunto())
    memcpy((char*)Num,(char*)Apa,sizeof(numeradores));
  else
    memcpy((char*)Num,(char*)Npa,sizeof(numeradores));
  for (i=0; i<=grandemax; i++)
    Nglobal.cf[i]=0.0;
  Nglobal.g=0;
  for (j=jmin-1; j<jmax; j++) {
      for (k=kmin-1; k<kmax; k++) {
          if (Adjunto())
	    kk=L[j][get_int(tsaida)];
          else
	    kk=C[j][get_int(tsaida)];
          if (kk!=0) {
              FORLIM2=Num[kk-1][k].g;
              for (i=0; i<=FORLIM2; i++) {
                  jj=i*fases+Num[kk-1][k].minpot;
                  Nglobal.cf[jj]+=Num[kk-1][k].cre[i];
                  if (Nglobal.g<jj)
                    Nglobal.g=jj;
              }
          }
      }
  }
  while (Nglobal.g>0&&fabs(Nglobal.cf[Nglobal.g])<get_real(tminimo)) Nglobal.g--;
}

#define imax 50

/* variables for CalcularRaizes: */
struct LOC_CalcularRaizes {
  polpequeno *peq;
  raizes *R;
} ;

void ConverterRaizes(struct LOC_CalcularRaizes *LINK)
{
  raizes NR,*WITH;
  double m,f,f1;
  short FORLIM;
  double TEMP,TEMP1;

  WITH=LINK->R;
  k=LINK->peq->minpot;
  NR.g=WITH->g*fases+k;
  for (i=1; i<=k; i++) {  /*Acrescentar ra¡zes em z=0*/
      NR.re[i-1]=0.0;
      NR.im[i-1]=0.0;
  }
  FORLIM=WITH->g;
  for (i=1; i<=FORLIM; i++) {
      if (WITH->re[i-1]==0) {
          f=M_PI/2;
          if (WITH->im[i-1]<0)
            f=-f;
      }
      else {
          f=atan(WITH->im[i-1]/WITH->re[i-1]);
          if (WITH->re[i-1]<0) {
              if (WITH->im[i-1]>0)
                f=M_PI+f;
              else
                f-=M_PI;
          }
      }
      if (WITH->re[i-1]==0&&WITH->im[i-1]==0)
        m=0.0;
      else {
          TEMP=WITH->re[i-1];
          TEMP1=WITH->im[i-1];
          m=Ex(sqrt(TEMP*TEMP+TEMP1*TEMP1),1.0/fases);
      }
      for (j=1; j<=fases; j++) {
          k++;
          f1=(f+(j-1)*2*M_PI)/fases;
          NR.re[k-1]=m*cos(f1);
          NR.im[k-1]=m*sin(f1);
      }
  }
  *LINK->R=NR;
}

void CalcularRaizes(polpequeno *peq_,polgrande *gnd,raizes *R_,
                           boolean calculandopolos,boolean global)
{  /*Programa principal CalcularRaizes*/
  struct LOC_CalcularRaizes V;
  coefgrande a1,a2,c1,c2;
  double tolm,t,tol,p1,p2,d,xr,xi,p,d1,d2,e1,e2;
  boolean feito;
  short nn,n,ordem;
  char STR2[256],STR3[256];
  double TEMP,TEMP1;

  V.peq=peq_;
  V.R=R_;
  if (global) {
      n=gnd->g;
      memcpy((char*)a1,(char*)gnd->cf,sizeof(coefgrande));
  }
  else {
      n=V.peq->g;
      for (i=0; i<=n; i++)
        a1[i]=V.peq->cre[i];
  }
  tol=get_real(ttolz);
  ordem=0;
  tolm=get_real(ttolp);
  xr=get_real(treal);
  xi=get_real(timag);
  feito=false;
  nn=0;
  V.R->g=n;
  if (n<1) {
      if (!global&&V.peq->minpot>0&&a1[0]!=0) {
	  sprintf(STR2,"%hd roots at z^(1/%hd)=0",
		  V.peq->minpot,fases);
	  puts(STR2);
          goto _LFim;
      }
      puts("* No roots to compute");
      return;
  }
  if (!calculandopolos) {
      for (i=0; i<=n; i++)
        a1[i]/=a1[n];
  }
  for (i=0; i<=n; i++)
    a2[i]=0.0;
  fputs("Computing...",stdout);
  /*Eliminacao de raizes na origem*/
  while (n>1&&a1[0]==0) {
      V.R->re[n-1]=0.0;
      V.R->im[n-1]=0.0;
      sprintf(STR3,"%hd ",n);
      fputs(STR3,stdout);
      n--;
      for (i=0; i<=n; i++)
        a1[i]=a1[i+1];
  }
  while (!feito) {
      if (n>1) {
          /*Calculo dos valores do polinomio (p) e de sua derivada (d)*/
          d1=a1[n];
          p1=d1;
          d2=a2[n];
          p2=d2;
          for (i=n-1; i>=0; i--) {
              p1=Rmult(p1,p2,xr,xi)+a1[i];
              p2=Ires+a2[i];
              if (i>0) {
                  d1=Rmult(d1,d2,xr,xi)+p1;
                  d2=Ires+p2;
              }
          }
          /*Calculo do erro. Esta forma dificulta overflow*/
          if (d1==0||d2==0) {
              d=d1*d1+d2*d2;
              e1=(p1*d1+p2*d2)/d;
              e2=(p2*d1-p1*d2)/d;
          }
          else {
              d=d1/d2+d2/d1;
              e1=(p1/d2+p2/d1)/d;
              e2=(p2/d2-p1/d1)/d;
          }
          /*Testa possivel raiz multipla*/
          d=fabs(d1)+fabs(d2);
          p=fabs(p1)+fabs(p2);
          if (d<tolm&&p<tolm) {
              /*deriva o polinomio e continua*/
              if (ordem==0) {
                  memcpy((char*)c1,(char*)a1,sizeof(coefgrande));
                  memcpy((char*)c2,(char*)a2,sizeof(coefgrande));
              }
              for (i=1; i<=n; i++) {
                  a1[i-1]=a1[i]*i/n;
                  a2[i-1]=a2[i]*i/n;
              }
              n--;
              ordem++;
              fputs("+",stdout);
              continue;
          }
          /*Atualiza raizes*/
          xr-=e1;
          xi-=e2;
          /*Testa convergˆncia*/
          t=fabs(e1)+fabs(e2);
          if (t<tol) {
              /*Armazena raizes calculadas*/
              for (i=n+ordem; i>=n; i--) {
		  sprintf(STR3,"%hd ",i);
                  fputs(STR3,stdout);
                  V.R->re[i-1]=xr;
                  V.R->im[i-1]=xi;
              }
              /*Repoe polinomio original, se for o caso*/
              if (ordem>0) {
                  memcpy((char*)a1,(char*)c1,sizeof(coefgrande));
                  memcpy((char*)a2,(char*)c2,sizeof(coefgrande));
                  n+=ordem;
              }
              /*Deflaciona polinomio*/
              for (i=0; i<=ordem; i++) {
                  for (j=n-1; j>=1; j--) {
                      /* Ha alguma otimizacao que faz isto nao funcionar (I?)*/
                      a1[j]=Rmult(a1[j+1],a2[j+1],xr,xi)+a1[j];
                      a2[j]=Ires+a2[j];
                  }
                  n--;
                  for (j=0; j<=n; j++) {
                      a1[j]=a1[j+1];
                      a2[j]=a2[j+1];
                  }
              }
              /*Prepara calculo da proxima raiz (igual ao EletSim)*/
              if (fabs(xi)>0.01)
                xi=-xi;
              else
                xi=0.1;
              if (ordem>0)   /*evita derivada 0 a seguir*/
                xr-=0.01;
              ordem=0;
              nn=0;
              continue;
          }
          nn++;
          /*Demorando a convergir*/
          if (nn<=imax)
            continue;
	  puts("\n* Convergence problems:");
	  if (ordem>0) {
	      sprintf(STR3,"* Root of multiplicity %hd",ordem+1);
	      puts(STR3);
	  }
	  sprintf(STR3,"  Present error:       %g",t);
	  puts(STR3);
	  sprintf(STR3,"  Polynomial magnitude:%g",p);
	  puts(STR3);
	  sprintf(STR3,"  Derivative magnitude:%g",d);
	  puts(STR3);
	  sprintf(STR3,"  Tol. for magnitudes: %g",tolm);
	  puts(STR3);
	  sprintf(STR3,"  Real approximation:  %g",xr);
	  puts(STR3);
	  sprintf(STR3,"  Imag approximation:  %g",xi);
	  puts(STR3);
	  tol*=10;
	  sprintf(STR3,"  Tol. for error increased to %g",tol);
	  puts(STR3);
	  nn=0;
	  continue;
      }
      TEMP=a1[1];
      TEMP1=a2[1];
      /*Ultimas raizes*/
      d=-(TEMP*TEMP+TEMP1*TEMP1);
      xr=(a1[0]*a1[1]+a2[0]*a2[1])/d;
      xi=(a2[0]*a1[1]-a1[0]*a2[1])/d;
      feito=true;
      nn=0;
      for (i=n+ordem; i>=n; i--) {
	  sprintf(STR3,"%hd ",i);
          fputs(STR3,stdout);
       	  V.R->re[i-1]=xr;
	  V.R->im[i-1]=xi;
      }
  }
  puts("");
_LFim:
  if (!global)
    ConverterRaizes(&V);
  if (calculandopolos)
    polos_validos=true;
  else
    zeros_validos=true;
}  /*CalcularRaizes*/

#undef imax

void CalcularPoloseZeros(void)
{
  char STR1[256];
  char STR2[256];

  if (!polos_validos) {
      puts("Computing roots of denominator");
      CalcularRaizes(&Nden,&Nglobal,&Polos,true,false);
  }
  if (zeros_validos)
    return;
  sprintf(STR2,"Computing roots of %s",NomeAtual(STR1));
  puts(STR2);
  if (get_sel(stiponum)==1) {
      GerarGlobal();
      CalcularRaizes(&Nden,&Nglobal,&Zeros,false,true);
      return;
  }
  if (Adjunto()) {
      k=L[get_int(tfj)-1][get_int(tsaida)];
      if (k!=0)
	CalcularRaizes(&Apa[k-1][get_int(tfk)-1],&Nglobal,&Zeros,
                       false,false);
      else
	puts("* No roots to compute");
      return;
  }
  k=C[get_int(tfj)-1][get_int(tsaida)];
  if (k!=0)
    CalcularRaizes(&Npa[k-1][get_int(tfk)-1],&Nglobal,&Zeros,
                   false,false);
  else
    puts("* No roots to compute");
}

void ListarRaizes(raizes *R, char* titulo)
{
  char STR2[256];

  sprintf(STR2,"%s roots in the z^(1/%hd) domain:",
	  titulo,fases);
  puts(STR2);
  for (i=1; i<=R->g; i++) {
      sprintf(txt,"z(%hd):%g",i,R->re[i-1]);
      if (fabs(R->im[i-1])>get_real(ttolz))
	sprintf(txt+strlen(txt)," %gj",R->im[i-1]);
      puts(txt);
  }
}

void IniciarGrafico(Xv_opaque painel,double x1,double x2,double y1,
			   double y2,short xmax,short ymax,boolean xlog)
{
  double ax,bx,ay,by,t1,t2;
  char STR1[256];
  char STR3[256];

  XSetForeground(Gdisplay,Ggc,cor[0]);
  XSetFunction(Gdisplay,Ggc,GXcopy);
  XFillRectangle(Gdisplay,Gxid,Ggc,0,0,get_dx(painel),get_dy(painel));
  ay=(ymax-ymin)/(y1-y2);
  by=ymax-ay*y1;
  if (!xlog) {
      ax=(xmax-xmin)/(x2-x1);
      bx=xmin-ax*x1;
  }
  else {
      ax=(xmax-xmin)/log(x2/x1);
      bx=xmin-ax*log(x1);
  }
  if (x2<=x1||y2<=y1)
    grade=false;
  if (grade) {
      XSetLineAttributes(Gdisplay,Ggc,0,LineOnOffDash,CapButt,JoinMiter);
      XSetForeground(Gdisplay,Ggc,cor[6]);
      if (xlog&&x2-x1>x1)
        t1=x1;
      else
        t1=x2-x1;
      t1=exp(log(10.0)*floor(log(t1)/log(10.0)-0.499999+0.5));
      t2=floor(x1/t1+0.5+0.5)*t1;
      while (t2<x2) {
          if (!xlog) {
              i=(short)floor(ax*t2+bx+0.5);
              XDrawLine(Gdisplay,Gxid,Ggc,i,ymin,i,ymax);
              t2+=t1;
              continue;
          }
          if ((short)floor(t2/t1+0.5)==10) {
              t1=10*t1;
              XSetForeground(Gdisplay,Ggc,cor[2]);
          }
          i=(short)floor(ax*log(t2)+bx+0.5);
          XDrawLine(Gdisplay,Gxid,Ggc,i,ymin,i,ymax);
          t2+=t1;
          XSetForeground(Gdisplay,Ggc,cor[6]);
      }
      t1=y2-y1;
      t1=exp(log(10.0)*floor(log(t1)/log(10.0)-0.5+0.5));
      t2=floor(y1/t1+0.5+0.5)*t1;
      while (t2<y2) {
          i=(short)floor(ay*t2+by+0.5);
          XDrawLine(Gdisplay,Gxid,Ggc,xmin,i,xmax,i);
          t2+=t1;
      }
  }
  XSetLineAttributes(Gdisplay,Ggc,0,LineSolid,CapButt,JoinMiter);
  XSetForeground(Gdisplay,Ggc,cor[1]);
  XDrawLine(Gdisplay,Gxid,Ggc,0,ymax,xmax,ymax);
  XDrawLine(Gdisplay,Gxid,Ggc,xmin,ymin,xmin,get_dy(painel));
  sprintf(txt,"%5.1f",y2);
  XDrawString(Gdisplay,Gxid,Ggc,0,ymin+txth,txt,strlen(txt));
  sprintf(txt,"%5.1f",y1);
  XDrawString(Gdisplay,Gxid,Ggc,0,ymax-2,txt,strlen(txt));
  sprintf(txt,"%8.3f",x1);
  while (txt[0]==' ') {
      strcpy(STR1,txt+1);
      strcpy(txt,STR1);
  }
  XDrawString(Gdisplay,Gxid,Ggc,xmin+2,ymax+txth,txt,strlen(txt));
  sprintf(txt,"%8.3f",x2);
  XDrawString(Gdisplay,Gxid,Ggc,xmax-64,ymax+txth,txt,strlen(txt));
  sprintf(STR3,"ASIZ - %s %s",rede,NomeAtual(STR1));
  XDrawString(Gdisplay,Gxid,Ggc,1,txth,STR3,strlen(STR3));
}

void Falha(void)
{
  puts("* Failure in writting file");
}

void EscreverTabelaFrequencia(void)
{
  char STR1[256];
  char STR2[14];
  double t;
 
  ioresult=fprintf(arquivo,"\nFrequency response\n");
  ioresult=fprintf(arquivo,"Numerator: %s; Sw. frequency=%g Hz; Output: ",
		 NomeAtual(STR1),
		 get_real(tfs));
  if (get_sel(ssh)==0)
    ioresult=fprintf(arquivo,"S/H");
  else if (get_sel(ssh)==1)
    ioresult=fprintf(arquivo,"Impulse");
  else ioresult=fprintf(arquivo,"No sampling");
  if (plotardesvios) {
      if (Estatistico())
	ioresult=fprintf(arquivo,"; Statistical dev.");
      else
	ioresult=fprintf(arquivo,"; Deterministic dev.");
      ioresult=fprintf(arquivo,"; Var=%g",get_real(tvar));
  }
  ioresult=fprintf(arquivo,"\n\n");
  sprintf(STR2,"Freq. (%s)",unid[get_sel(srads)]);
  ioresult=fprintf(arquivo,"%*s%*s%*s%*s",cm,STR2,cm,"Gain (dB)",cm,"Phase (deg)",cm,"Delay (s)");
  if (plotardesvios)
    ioresult=fprintf(arquivo,"%*s%*s%*s%*s",cm,"DevG (dB)",cm,"DevP (deg)",
      cm,"Gain-DevG (dB)",cm,"Gain+DevG (dB)");
  ioresult=fprintf(arquivo,"\n\n");
  for (i=0; i<=ultimof; i++) {
      ioresult=fprintf(arquivo,"%*.*f%*.*f%*.*f%*g",
		     cm,dc,Frq[i],cm,dc,Gan[i],cm,dc,
		     Ang[i],cm,Tg[i]);
      if (plotardesvios) {
        t=get_real(tvar);
	ioresult=fprintf(arquivo,"%*.*f%*.*f%*.*f%*.*f",
		       cm,dc,t*Dgan[i],
                       cm,dc,t*Dang[i],
                       cm,dc,Gan[i]-t*Dgan[i],
                       cm,dc,Gan[i]+t*Dgan[i]
                       );
      }
      ioresult=putc('\n',arquivo);
  }
  if (ioresult!=EOF)
    puts("Frequency response table written");
  else
    Falha();
}

void EscreverTabelaTransiente(void)
{
  char STR1[256];

  ioresult=fprintf(arquivo,"\nTransient response:\nInput: %g A ",
		 get_real(tampl));
  switch (get_sel(sinput)) {

    case 2:
      sprintf(txt,"sinusoid: %g Hz, %g degrees",
	      get_real(tfreq),
	      get_real(tfase));
      break;

    case 1:
      strcpy(txt,"impulse");
      break;

    case 0:
      strcpy(txt,"step");
      break;
  }
  ioresult=fprintf(arquivo,"%s\n",txt);
  ioresult=fprintf(arquivo,"Numerator: %s; Sw. frequency=%g Hz\n",
		 NomeAtual(STR1),
		 get_real(tfs));
  ioresult=fprintf(arquivo,"\n%*s%*s%*s\n\n",
		 cm,"Time (s)",cm,"Vi (V)",cm,"Vo (V)");
  for (i=0; i<=ultimot; i++)
    ioresult=fprintf(arquivo,"%*.*f%*.*f%*.*f\n",
		   cm,dc,Tempo[i],cm,dc,Vi[i],cm,dc,Vo[i]);
  if (ioresult!=EOF)
    puts("Transient response table written");
  else
    Falha();
}

void AbrirJRelatorio(tipotabela porque)
{
  if (!netlist_valido) {
      puts("* No netlist read");
      return;
  }
  sprintf(get_text(trelatorio),"%s.siz",rede);
  asalvar=porque;
  open_window(jrelatorio);
}

void ListarDenominador(void)
{
  if (!AnaliseValida())
    return;
  puts("Denominator:");
  ListarPequeno(&Nden);
}

notify_button(InvalidarNumerador)
{
  zeros_validos=false;
  frequencia_valida=false;
  transiente_valido=false;
}

notify_textfield(InvalidarAnalise)
{
  analise_valida=false;
  zeros_validos=false;
  polos_validos=false;
  frequencia_valida=false;
  transiente_valido=false;
  xv_set(ganalise,PANEL_VALUE,0,NULL);
  return PANEL_NEXT;
}

notify_textfield(InvalidarFrequencia)
{
  frequencia_valida=false;
  return PANEL_NEXT;
}

notify_textfield(InvalidarRaizes)
{
  polos_validos=false;
  zeros_validos=false;
  return PANEL_NEXT;
}

notify_textfield(InvalidarTransiente)
{
  transiente_valido=false;
  return PANEL_NEXT;
}

notify_textfield(InvalidarNetlist)
{
  netlist_valido=false;
  InvalidarAnalise(NULL,NULL);
  puts("Read again the netlist file to see the effect");
  return PANEL_NEXT;
}

/* variables for LerNetList: */
struct LOC_LerNetList {
  short maior,menor;
} ;

void Ordenar(short a,short b,struct LOC_LerNetList *LINK)
{
  char STR1[256];

  if (a>b) {
      LINK->maior=a;
      LINK->menor=b;
      return;
  }
  if (a<b) {
      LINK->maior=b;
      LINK->menor=a;
  }
  else {
      sprintf(STR1,"%s: Forbidden circuit",txt);
      ErroFatal(STR1);
  }
}

void MaisUm(void)
{
  char STR2[256];

  e++;
  if (e>elmax) {
      sprintf(STR2,"The maximum number of effective elements is %hd",elmax);
      ErroFatal(STR2);
  }
}

void Somar(apontadores C,short a,short b,short f,
		 struct LOC_LerNetList *LINK)
{
  /*"Soma" linhas ou colunas*/
  short i,j;

  Ordenar(C[f-1][a],C[f-1][b],LINK);
  for (i=0; i<fases; i++) {
      for (j=1; j<=variaveis; j++) {
          if (C[i][j]==LINK->maior)
            C[i][j]=LINK->menor;
          if (C[i][j]>LINK->maior)
            C[i][j]--;
      }
  }
}

void TestarVariaveis(void)
{
  char STR2[256];

  if (variaveis>nosmax) {
      sprintf(STR2,"The maximum number of variables is %hd",nosmax);
      ErroFatal(STR2);
  }
}

void SomarEquacoes(short a,short b,short *x,struct LOC_LerNetList *LINK)
{
  /*"Soma" linhas, alocando a eq. "maior" para x*/
  short i,j;

  variaveis++;
  TestarVariaveis();
  *x=variaveis;
  for (i=0; i<fases; i++) {
      Ordenar(L[i][a],L[i][b],LINK);
      for (j=1; j<=variaveis; j++) {
	  if (L[i][j]==LINK->maior)
	    L[i][j]=LINK->menor;
      }
      L[i][variaveis]=LINK->maior;
      C[i][variaveis]=0;
  }
}

void TestarFase(short f)
{
  char STR1[256];

  if (f<1||f>fases) {
      sprintf(STR1,"%s: Invalid phase",txt);
      ErroFatal(STR1);
  }
}

notify_button(LerNetList)
{
  struct LOC_LerNetList V;
  double Gm0,Gds;
  short ng,ns,nd;
  char mnome[tamnome+1];
  Xv_opaque WITH;
  char STR1[256];
  char STR2[256];
  char STR3[256];
  char STR4[256];
  char STR5[256];
  _REC_NetList *WITH1;
  char STR7[256];
  char STR9[12];
  _REC_NetList *WITH2;
  double DUMMY;

  close_window(jnetlist);
  /*close_window(jdiretorio);*/
  if (relatorio) {
      fclose(arquivo);
      relatorio=false;
      puts("Report file closed");
  }
  ok=false;
  WITH=tnetlist;
  if (pos('.',get_text(tnetlist))==0) {
      strcat(get_text(tnetlist),".net");
  }
  sprintf(rede,"%.*s",pos('.',get_text(tnetlist))-1,get_text(tnetlist));
  arquivo=fopen(get_text(tnetlist),"r");
  ok=(arquivo!=0);
  if (!ok) {
      sprintf(STR2,"* File %s not found",get_text(tnetlist));
      puts(STR2);
      return;
  }
  sprintf(STR1,"Reading file %s",get_text(tnetlist));
  puts(STR1);
  fscanf(arquivo,"%hd%*[^\n]",&nos); /* Deve funcionar com ou sem ^M */
  variaveis=nos;
  sprintf(STR4,"Number of nodes: %hd",nos);
  puts(STR4);
  TestarVariaveis();
  fases=get_int(tfases);
  fasesatual=fases;
  equacoes=nos*fases;
  for (i=1; i<=fases; i++) {
      for (j=0; j<=nos; j++) {
	  if (j==0)
	    k=0;
	  else
	    k=j+(i-1)*nos;
	  C[i-1][j]=k;
	  L[i-1][j]=k;
      }
  }
  puts("Circuit description:");
  e=0;
  while (fscanf(arquivo,"%s",STR1)!=EOF) {
      MaisUm();
      WITH1=&NetList[e-1];
      STR1[5]='\0';
      strcpy(WITH1->nome,STR1);
      sprintf(txt,"%s: ",WITH1->nome);
      switch (WITH1->nome[0]) {

	case 'V':
	  fscanf(arquivo,"%hd%hd%lg%*[^\n]",&WITH1->n1,&WITH1->n2,
		 &WITH1->UU.U3.Vs);
	  getc(arquivo);
	  sprintf(txt+strlen(txt),"%hd(v+),%hd(v-),%g(Vs)",
		  WITH1->n1,WITH1->n2,WITH1->UU.U3.Vs);
	  WITH1->tipo=fonteV;
	  SomarEquacoes(WITH1->n1,WITH1->n2,&WITH1->UU.U3.nox,&V);
	  break;

	case 'E':
	case 'A':
	  if (WITH1->nome[0]=='E') {
	      fscanf(arquivo,"%hd%hd%hd%hd%lg%*[^\n]",&WITH1->n1,&WITH1->n2,
		     &WITH1->UU.U7.n3c,&WITH1->UU.U7.n4c,&WITH1->UU.U7.Av);
	      getc(arquivo);
	  }
	  else {
	      fscanf(arquivo,"%hd%hd%hd%lg%*[^\n]",&WITH1->UU.U7.n4c,
		     &WITH1->UU.U7.n3c,&WITH1->n1,&WITH1->UU.U7.Av);
	      getc(arquivo);
	      WITH1->n2=0;
	  }
	  sprintf(txt+strlen(txt),"%hd(vo+),%hd(vo-),%hd(vi+),%hd(vi-),%g(Av)",
		  WITH1->n1,WITH1->n2,WITH1->UU.U7.n3c,WITH1->UU.U7.n4c,
		  WITH1->UU.U7.Av);
	  WITH1->tipo=VCVS;
	  SomarEquacoes(WITH1->n1,WITH1->n2,&WITH1->UU.U7.noxc,&V);
	  break;

	case 'M':
	  strcpy(mnome,WITH1->nome);
	  fscanf(arquivo,"%hd%hd%hd%lg%lg%*[^\n]",&nd,&ng,&ns,&Gm0,&Gds);
	  getc(arquivo);
	  WITH1->tipo=VCCS;
	  sprintf(STR9,"Gm_%s",WITH1->nome);
	  strcpy(WITH1->nome,STR9);
	  WITH1->n1=nd;
	  WITH1->n2=ns;
	  WITH1->UU.U6.n3=ng;
	  WITH1->UU.U6.n4=ns;
	  WITH1->UU.U6.Gm=Gm0;
	  sprintf(txt+strlen(txt),"%hd(d),%hd(g),%hd(s),%g(Gm)",
		  WITH1->n1,WITH1->UU.U6.n3,WITH1->n2,WITH1->UU.U6.Gm);
	  if (get_sel(sgds)==1)
	    Gds=Gm0*get_real(tgds);
	  if (Gds!=0.0) {
	      MaisUm();
	      WITH2=&NetList[e-1];
	      WITH2->tipo=resistor;
	      sprintf(WITH2->nome,"Rd_%s",mnome);
	      WITH2->n1=nd;
	      WITH2->n2=ns;
	      WITH2->UU.Res=1/Gds;
	      sprintf(txt+strlen(txt),",%g(Gds)",Gds);
	  }
	  MaisUm();
	  WITH2=&NetList[e-1];
	  WITH2->tipo=capacitor;
	  sprintf(WITH2->nome,"Cgs%s",mnome);
	  WITH2->n1=ng;
	  WITH2->n2=ns;
	  if (get_sel(scap)==0)
	    WITH2->UU.Cap=1.0;
	  else {
	      WITH2->UU.Cap=Gm0*get_real(tcgs);
	      sprintf(txt+strlen(txt),",%g(Cgs)",WITH2->UU.Cap);
	  }
	  if (get_sel(scap)==1 && get_real(tcgd)!=0) {
	      MaisUm();
	      WITH2=&NetList[e-1];
	      WITH2->tipo=capacitor;
	      sprintf(WITH2->nome,"Cgd%s",mnome);
	      WITH2->n1=ng;
	      WITH2->n2=nd;
	      WITH2->UU.Cap=Gm0*get_real(tcgd);
	      sprintf(txt+strlen(txt),",%g(Cgd)",WITH2->UU.Cap);
	  }
	  break;

	case 'R':
	  fscanf(arquivo,"%hd%hd%lg%*[^\n]",&WITH1->n1,&WITH1->n2,
		 &WITH1->UU.Res);
	  getc(arquivo);
	  sprintf(txt+strlen(txt),"%hd(a),%hd(b),%g(R)",
		  WITH1->n1,WITH1->n2,WITH1->UU.Res);
	  WITH1->tipo=resistor;
	  break;

	case 'G':
	  fscanf(arquivo,"%hd%hd%hd%hd%lg",&WITH1->n1,&WITH1->n2,
		 &WITH1->UU.U6.n3,&WITH1->UU.U6.n4,&WITH1->UU.U6.Gm);
	  sprintf(txt+strlen(txt),"%hd(i+),%hd(i-),%hd(v+),%hd(v-),%g(Gm)",
		  WITH1->n1,WITH1->n2,WITH1->UU.U6.n3,WITH1->UU.U6.n4,
		  WITH1->UU.U6.Gm);
	  WITH1->tipo=VCCS;
	  break;

	case 'C':
	  fscanf(arquivo,"%hd%hd%lg%*[^\n]",&WITH1->n1,&WITH1->n2,
		 &WITH1->UU.Cap);
	  getc(arquivo);
	  sprintf(txt+strlen(txt),"%hd(a),%hd(b),%g(C)",
		  WITH1->n1,WITH1->n2,WITH1->UU.Cap);
	  WITH1->tipo=capacitor;
	  break;

	case 'I':
	  fscanf(arquivo,"%hd%hd%lg%*[^\n]",&WITH1->n1,&WITH1->n2,
		 &WITH1->UU.Is);
	  getc(arquivo);
	  sprintf(txt+strlen(txt),"%hd(i+),%hd(i-),%g(Is)",
		  WITH1->n1,WITH1->n2,WITH1->UU.Is);
	  WITH1->tipo=fonteI;
	  break;

	case 'S':
	  fscanf(arquivo,"%hd%hd",&WITH1->n1,&WITH1->n2);
	  sprintf(txt+strlen(txt),"%hd(a),%hd(b)",
		  WITH1->n1,WITH1->n2);
	  do {
	    k=fscanf(arquivo,"%c",&ch);
	    if (k!=EOF && ch==' ') {
	      fscanf(arquivo,"%hd",&WITH1->UU.fase);
	      TestarFase(WITH1->UU.fase);
	      Somar(C,WITH1->n1,WITH1->n2,WITH1->UU.fase,&V);
	      Somar(L,WITH1->n1,WITH1->n2,WITH1->UU.fase,&V);
	      equacoes--;
	      sprintf(txt+strlen(txt),",%hd",WITH1->UU.fase);
	    }
	  }
	  while (ch!='\n' && k!=EOF);
	  e--;
	  break;

	case 'O':
	  fscanf(arquivo,"%hd%hd%hd",&WITH1->n1,&WITH1->n2,&WITH1->UU.nout);
	  sprintf(txt+strlen(txt),"%hd(-/+),%hd(+/-),%hd(vo)",
		  WITH1->n1,WITH1->n2,WITH1->UU.nout);
	  for (i=1; i<=fases; i++) {
		  /*Amp. Ops. n„o s„o guardados tamb‚m*/
		      Somar(C,WITH1->n1,WITH1->n2,i,&V);
	      Somar(L,0,WITH1->UU.nout,i,&V);
	      equacoes--;
	  }
	  e--;
	  break;

	case '*':
	  fgets(txt,256,arquivo);
	  e--;
	  break;

	default:
	  sprintf(STR3,"%s Unknown element",txt);
	  ErroFatal(STR3);
	  break;
      }
      puts(txt);
  }
  fclose(arquivo);
  elementos=e;
  close_window(jsensi);
  for (e=1; e<=elementos; e++) {
      WITH1=&NetList[e-1];
      WITH1->selecionado=(WITH1->tipo==VCCS);
      WITH1->grupo='*';
  }
  sprintf(STR7,"Number of effective elements: %hd",elementos);
  puts(STR7);
  sprintf(STR7,"Equations in the resulting system: %hd",equacoes);
  puts(STR7);
  if (equacoes>linmax) {
      sprintf(STR7,"The maximum number of equations is %hd",linmax);
      ErroFatal(STR7);
  }
  sprintf(STR7,"Number of variables: %hd",variaveis);
  puts(STR7);

  /*O algor¡tmo abaixo funciona corretamente se n„o existirem elementos
    resistivos que fiquem ligados apenas a capacitores em alguma fase,
    quando o grau m ximo ser  subestimado e sistema ser  singular*/

  for (i=0; i<=equacoes; i++)
    Eqcap[i]=true;
  for (e=1; e<=elementos; e++) {
      WITH1=&NetList[e-1];
      if (WITH1->tipo!=capacitor) {
	  for (i=1; i<=fases; i++) {
	      Eqcap[L[i-1][WITH1->n1]]=false;
	      Eqcap[L[i-1][WITH1->n2]]=false;
	      if (WITH1->tipo==fonteV||WITH1->tipo==VCVS)
		Eqcap[L[i-1][WITH1->UU.U3.nox]]=false;
	  }
      }
  }
  /*O m ximo grau de polin“mio que aparece ‚ o n£mero de equa‡”es capacitivas*/
  capacitivas=0;
  for (i=1; i<=equacoes; i++) {
      if (Eqcap[i])
	capacitivas++;
  }
  maxz=capacitivas;
  i=maxz/fases;
  if (modf((double)maxz/fases,&DUMMY)!=0) {
      i++;
      sprintf(STR5,"Introduced %hd extra zeros/poles at zero in z^(1/%hd)",
	      maxz%fases,fases);
      puts(STR5);
  }
  sprintf(STR7,"Maximum complexity order (in z): %hd",i);
  puts(STR7);
  set_int(tgrau,i);
  set_max(tfk,fases);
  set_max(tfj,fases);
  netlist_valido=true;
  InvalidarAnalise(NULL,NULL);
  set_max(tnsaida,variaveis);
  set_max(tsaida,variaveis);
  if (get_int(tsaida)>variaveis) set_int(tsaida,1);
  if (get_int(tnsaida)>variaveis) set_int(tsaida,1);
  open_window(jpanalise);
}  /*LerNetList*/

notify_button(AnalisarCircuito)
{
  if (!netlist_valido) {
      puts("* No netlist read");
      return;
  }
  if (!analise_valida) {
      AnalisarNoCirculo();
      InterpolarPolinomios();
      analise_valida=true;
  }
  close_window(jpanalise);
  ListarDenominador();
  open_window(jpnumerador);
  open_window(jpfrequencia);
}

notify_textfield(InvalidarDesvios)
{
  if (get_sel(ssensi)!=0) {
    desvios_validos=false;
    return PANEL_NEXT;
  }
  if (!frequencia_valida)
    desvios_validos=false;
  if (!desvios_validos)
    frequencia_valida=false;
  open_window(jpfrequencia);
  return PANEL_NEXT;
}

notify_canvas(PlotarSensi)
{
  int x,y;
  _REC_NetList *WITH;
  char STR1[256];

#define largura 100
#define altura 15
  if (!Spronto) {
    Sdisplay=dpy;
    Sxid=xwin;
    Sgc=DefaultGC(dpy,DefaultScreen(dpy));
    Spronto=1;
    return;
  }
  if (!netlist_valido) return;
  Gdisplay=Sdisplay; Gxid=Sxid, Ggc=Sgc;
  XSetForeground(Gdisplay,Ggc,cor[1]);
  XSetFunction(Gdisplay,Ggc,GXcopy);
  XFillRectangle(Gdisplay,Gxid,Ggc,0,0,get_dx(csensi),get_dy(csensi));
  XSetForeground(Gdisplay,Ggc,cor[0]);
  npl=get_dx(csensi)/largura;
  for (e=1; e<=elementos; e++) {
      WITH=&NetList[e-1];
      x=(e-1)%npl*largura+1;
      y=(e-1)/npl*altura+txth;
      XDrawString(Gdisplay,Gxid,Ggc,x+10,y,WITH->nome,strlen(WITH->nome));
      if (WITH->selecionado) {
          sprintf(STR1,"%c",WITH->grupo);
          XDrawString(Gdisplay,Gxid,Ggc,x,y,STR1,strlen(STR1));
      }
  }
  XDrawString(Gdisplay,Gxid,Ggc,1,y+txth,"Prefixes a..z: correlated groups; *: uncorrelated",50);
  XDrawString(Gdisplay,Gxid,Ggc,1,y+2*txth,"Change w/mouse and [a]..[z], [*] keys",38);
  XDrawString(Gdisplay,Gxid,Ggc,1,y+3*txth,"Press [s] in the fr. resp. graph to list sensitivities",54);
}

event_canvas(MudarElementos)
{
  short x,y;
  _REC_NetList *WITH;
  char STR1[256];

  if (!Spronto) return;
  if (!netlist_valido) return;
  Gdisplay=Sdisplay; Gxid=Sxid, Ggc=Sgc;
  if (event_id(event)=='*'||(event_id(event)>='a'&&event_id(event)<='z')) {
    grupoatual=(char)event_id(event);
    return;
  }
  if ((event_id(event)!=MS_LEFT) && (event_id(event)!=MS_MIDDLE)) return; /*!!! Tentar melhorar isto */
    x=event_x(event)/largura+1;
  if (x>npl)
    return;
  e=(event_y(event)-5)/altura*npl+x;
  if (e<=0||e>elementos)
    return;
  WITH=&NetList[e-1];
  x=(e-1)%npl*largura+1;
  y=(e-1)/npl*altura;
  WITH->selecionado=(event_id(event)==MS_LEFT);
  XSetForeground(Gdisplay,Ggc,cor[1]);
  XFillRectangle(Gdisplay,Gxid,Ggc,x,y,9,txth);
  if (WITH->selecionado) {
      WITH->grupo=grupoatual;
      sprintf(STR1,"%c",WITH->grupo);
      XSetForeground(Gdisplay,Ggc,cor[0]);
      XDrawString(Gdisplay,Gxid,Ggc,x,y+txth,STR1,strlen(STR1));
  }
  frequencia_valida=false;
}

short Ly(double y)
{
  if (y>yfmax)
    y=yfmax;
  else if (y<ymin)
    y=ymin;
  return((short)floor(y+0.5));
}

/* variables for PlotarTransferencia: */
struct LOC_PlotarTransferencia {
  polpequeno *Nden;
  double na,nb,ta,tb,da,db;
} ;

double Nx(polpequeno *Num)
{
  double ta,tb,t;
  short i,FORLIM;

  if (Num->valido) {
    Ires=Num->valb;
    return Num->vala;
  }
  ta=0.0;
  tb=0.0;
  for (i=Num->g; i>=0; i--) {
    t=ta*z1-tb*z2+Num->cre[i];
    tb=ta*z2+tb*z1;
    ta=t;
  }
  FORLIM=Num->minpot;
  for (i=1; i<=FORLIM; i++) {
    ta=Rmult(ta,tb,z1f,z2f);
    tb=Ires;
  }
  Ires=tb;
  Num->vala=ta;
  Num->valb=tb;
  Num->valido=true;
  return ta;
}

double dEdGm(short na,short nb,short nc,short nd,short j,short k,
		   short f1,short f2,boolean capacitivo)
{
  double va,vb,aa,ab;
  short kk;

  /*dEojk/dGmf1f2=(Ncf1k-Ndf1k)(Aaf2j-Abf2j)/(DnDa)*/
  kk=C[f1-1][nc];
  if (kk!=0) {
    va=Nx(&Npa[kk-1][k-1]);
    vb=Ires;
  }
  else {
    va=0.0;
    vb=0.0;
  }
  kk=C[f1-1][nd];
  if (kk!=0) {
    va-=Nx(&Npa[kk-1][k-1]);
    vb-=Ires;
  }
  kk=L[f2-1][na];
  if (capacitivo&&!Eqcap[kk])
    kk=0;
  if (kk!=0) {
    aa=Nx(&Apa[kk-1][j-1]);
    ab=Ires;
  }
  else {
    aa=0.0;
    ab=0.0;
  }
  kk=L[f2-1][nb];
  if (capacitivo&&!Eqcap[kk])
    kk=0;
  if (kk!=0) {
    aa-=Nx(&Apa[kk-1][j-1]);
    ab-=Ires;
  }
  return(Rmult(va,vb,aa,ab));
  /*Ainda nao divide por DnDa*/
}

void SGm(short n1,short n2,short n3,short n4,double Gm,
               struct LOC_PlotarTransferencia *LINK)
{
  short i,j,k;

  for (j=jmin; j<=jmax; j++) {
    for (k=kmin; k<=kmax; k++) {
      for (i=1; i<=fases; i++) {
	LINK->ta+=dEdGm(n1,n2,n3,n4,j,k,i,i,false);
        LINK->tb+=Ires;
      }
    }
  }
  LINK->ta=Rdiv(LINK->ta,LINK->tb,LINK->da,LINK->db);
  LINK->tb=Ires;
  LINK->ta=Rdiv(LINK->ta,LINK->tb,LINK->na,LINK->nb)*Gm;
  LINK->tb=Ires*Gm;
}

void SIs(short n1,short n2,double Is,
               struct LOC_PlotarTransferencia *LINK)
{
  short i,j,k;

  for (j=jmin-1; j<jmax; j++) {
    for (k=kmin-1; k<kmax; k++) {
      i=L[k][n1];
      if (i!=0) {
	LINK->ta+=Nx(&Apa[i-1][j]);
        LINK->tb+=Ires;
      }
      i=L[k][n2];
      if (i!=0) {
	LINK->ta-=Nx(&Apa[i-1][j]);
        LINK->tb-=Ires;
      }
    }
  }
  LINK->ta=Rdiv(LINK->ta,LINK->tb,LINK->na,LINK->nb)*Is;
  LINK->tb=Ires*Is;
}

void PlotarTransferencia(polgrande *Num,polpequeno *Nden_,
  double *Gan, double *Ang, double *Tg,
  short estilo,TCOR corganho,TCOR corfase,TCOR coratraso,
  int reter, boolean sensibilidade, boolean listar_resposta)
{
  struct LOC_PlotarTransferencia V;
  short i,j,k;
  double ea,eb,t,wt,an,ha,hb,sa,sb,t1,t2,t11,t22;
  double gsa[26],gsb[26];
  boolean gusado[26];
  polpequeno *WITH;
  _REC_NetList *WITH1;
  char STR1[256];
  double TEMP;

  V.Nden=Nden_;
  XSetLineAttributes(Gdisplay,Ggc,0,estilo,CapButt,JoinMiter);
  if (hf>ultimof||listar_resposta) {
      wt=w/get_real(tfs);
      if (Hertz()) wt=2*M_PI*wt;
      z1f=cos(wt/fases);
      z2f=sin(wt/fases);
      V.na=0.0;
      V.nb=0.0;
      for (i=Num->g; i>=0; i--) {
        t=V.na*z1f-V.nb*z2f+Num->cf[i];
        V.nb=V.na*z2f+V.nb*z1f;
        V.na=t;
      }
      z1=cos(wt);
      z2=sin(wt);
      WITH=V.Nden;
      V.da=0.0;
      V.db=0.0;
      for (i=WITH->g; i>=0; i--) {
        t=V.da*z1-V.db*z2+WITH->cre[i];
        V.db=V.da*z2+V.db*z1;
        V.da=t;
      }
      if (V.da==0||V.db==0) {
        t=V.da*V.da+V.db*V.db;
        if (t==0) t=1e-20;
        ea=(V.na*V.da+V.nb*V.db)/t;
        eb=(V.nb*V.da-V.na*V.db)/t;
      }
      else {
        t=V.da/V.db+V.db/V.da;
        ea=(V.na/V.db+V.nb/V.da)/t;
        eb=(V.nb/V.db-V.na/V.da)/t;
      }
      switch (reter) {
	case 0: /* S/H */  
          t=wt/fases;
          if (t==0) {ha=1/fases; hb=0;}
          else {ha=sin(t)/t/fases; hb=(cos(t)-1)/t/fases;}
          V.ta=Rmult(ea,eb,ha,hb); V.tb=Ires;
          break;
        case 1: /* Impulso */
          V.ta=ea/fases;
          V.tb=eb/fases;
          break;
        case 2: /* Sem amostragem */
          if (V.Nden->g*fases!=Num->g) an=0; else an=Num->cf[Num->g];
          t=wt/fases;
          if (t==0) {ha=1/fases; hb=0;}
          else {ha=sin(t)/t/fases; hb=(cos(t)-1)/t/fases;}
          ha=Rmult(ha,hb,z1f,z2f); hb=Ires;
          V.ta=Rmult(ea-an,eb,ha,hb)+an/fases; V.tb=Ires;
          break;
      }
      if (V.ta==0) {
        if (V.tb==0) V.tb=1e-11;
        V.ta=V.tb*1e-11;
      }
      if (!listar_resposta) {
        ModuloFase(V.ta,V.tb,&(Gan[hf]),&(Ang[hf]));
        if (hf>0) {
          t=Ang[hf-1]-Ang[hf];
          while (t>170) t-=180;
          while (t<-170) t+=180;
          Tg[hf]=M_PI/180*t/(w-Frq[hf-1]);
          if (Hertz()) Tg[hf]/=(2*M_PI);
        }
        else Tg[hf]=0;
        Frq[hf]=w;
      }
      /*Calculo de sensibilidades*/
      if (sensibilidade) {
        /* Assume-se (z1,z2)=Exp(jwT), (z1f,z2f)=Exp(jwT/f), Eo=(ea,eb)=(na,nb)/(da,db) */
          sa=0.0;
          sb=0.0;
          for (i=0; i<=25; i++) {
              gusado[i]=false;
              gsa[i]=0.0;
              gsb[i]=0.0;
          }
          /*Invalida todos os numeradores e o denominador*/
          for (i=0; i<equacoes; i++) {
              for (j=0; j<fases; j++) {
                  Npa[i][j].valido=false;
                  Apa[i][j].valido=false;
              }
          }
          V.Nden->valido=false;
          /*Calcula sensibilidades*/
          for (e=1; e<=elementos; e++) {
              WITH1=&NetList[e-1];
              if (WITH1->selecionado) {
                  V.ta=0.0;
                  V.tb=0.0;
                  switch (WITH1->tipo) {

                    case resistor:
                      SGm(WITH1->n1,WITH1->n2,WITH1->n1,WITH1->n2,
                          -1/WITH1->UU.Res,&V);
                      break;

                    case VCCS:
		      SGm(WITH1->n1,WITH1->n2,WITH1->UU.U6.n3,WITH1->UU.U6.n4,
                          WITH1->UU.U6.Gm,&V);
                      break;

                    case VCVS:
		      SGm(0,WITH1->UU.U3.nox,WITH1->n1,
                          WITH1->n2,-1/WITH1->UU.U7.Av,&V);
                      break;

                    case capacitor:
                      for (j=jmin; j<=jmax; j++) {
                          for (k=kmin; k<=kmax; k++) {
                              for (i=1; i<=fases; i++) {
				  t11=dEdGm(WITH1->n1,WITH1->n2,WITH1->n1,
					      WITH1->n2,j,k,i,i,true);
                                  t22=Ires;
				  t1=dEdGm(WITH1->n1,WITH1->n2,WITH1->n1,
					     WITH1->n2,j,k,
					     (i+fases-2)%fases+1,i,true);
				  t2=Ires;
                                  t1=Rdiv(t1,t2,z1f,z2f);
                                  t2=Ires;
                                  V.ta+=t11-t1;
                                  V.tb+=t22-t2;
                              }
                          }
                      }
                      V.ta=Rdiv(V.ta,V.tb,V.da,V.db);
                      V.tb=Ires;
                      V.ta=Rdiv(V.ta,V.tb,V.na,V.nb)*WITH1->UU.Cap;
                      V.tb=Ires*WITH1->UU.Cap;
                      break;

                    case fonteI:
                      SIs(WITH1->n1,WITH1->n2,WITH1->UU.Is,&V);
                      break;

                    case fonteV:
		      SIs(WITH1->UU.U3.nox,0,WITH1->UU.U3.Vs,&V);
                      break;

                    default:
                      ErroFatal("??!!");
                      break;
                  }
                  if (listar_resposta) {
		      sprintf(STR1,"%s: % *.*f%+*.*fj",
			WITH1->nome,(int)(intnome-strlen(WITH1->nome)+10),6,V.ta,9,6,V.tb);
		      puts(STR1);
                  }
                  if (Estatistico()) {
                      if (WITH1->grupo=='*') {
                          sa+=V.ta*V.ta;
                          sb+=V.tb*V.tb;
                      }
                      else {
                          i=WITH1->grupo-'a';
                          gusado[i]=true;
                          gsa[i]+=V.ta;
                          gsb[i]+=V.tb;
                      }
                  }
                  else {
                      sa+=V.ta;
                      sb+=V.tb;
                  }
              }
          }
          if (Estatistico()) {
              for (i=0; i<26; i++) {
                  if (gusado[i]) {
                      TEMP=gsa[i];
                      sa+=TEMP*TEMP;
                      TEMP=gsb[i];
		      sb+=TEMP*TEMP;
		      if (listar_resposta) {
			  sprintf(STR1,"Group %c:  %*.*f %*.*fj",
				  (char)(i+'a'),
				  9,6,gsa[i],
				  9,6,gsb[i]);
			  puts(STR1);
		      }
		  }
	      }
	      sa=sqrt(sa);
	      sb=sqrt(sb);
	  }
	  if (!listar_resposta) {
	      Dgan[hf]=8.685889638*sa;
	      Dang[hf]=57.29577951*sb;
	  }
      }
  }
  if (listar_resposta||hf<=0)
    return;
  /*Fase*/
  j=(short)floor((hf-1)*ah+bh+0.5);
  k=(short)floor(hf*ah+bh+0.5);
  if (plotarfase) {
      XSetForeground(Gdisplay,Ggc,corfase);
      XDrawLine(Gdisplay,Gxid,Ggc,j,(short)floor(af*Ang[hf-1]+bf+0.5),k,
	   (short)floor(af*Ang[hf]+bf+0.5));
  }
  /*Tg*/
  if (plotaratraso && hf>1) {
      XSetForeground(Gdisplay,Ggc,coratraso);
      XDrawLine(Gdisplay,Gxid,Ggc,j,Ly(ad*Tg[hf-1]+bd),k,Ly(ad*Tg[hf]+bd));
  }
  /*Ganho*/
  XSetForeground(Gdisplay,Ggc,corganho);
  XDrawLine(Gdisplay,Gxid,Ggc,j,Ly(ag*Gan[hf-1]+bg),k,Ly(ag*Gan[hf]+bg));
  if (!sensibilidade)
    return;
  /*Dfase*/
  j=(short)floor((hf-1)*ah+bh+0.5);
  k=(short)floor(hf*ah+bh+0.5);
  XSetForeground(Gdisplay,Ggc,cor[1]);
  XSetLineAttributes(Gdisplay,Ggc,0,LineOnOffDash,CapButt,JoinMiter);
  if (plotarfase) {
      XDrawLine(Gdisplay,Gxid,Ggc,j,Ly(af*(Ang[hf-1]+get_real(tvar)*Dang[hf-1])+bf),k,
	   Ly(af*(Ang[hf]+get_real(tvar)*Dang[hf])+bf));
      if (Estatistico())
	XDrawLine(Gdisplay,Gxid,Ggc,j,Ly(af*(Ang[hf-1]-get_real(tvar)*Dang[hf-1])+bf),k,
	     Ly(af*(Ang[hf]-get_real(tvar)*Dang[hf])+bf));
  }
  /*Dganho*/
  XDrawLine(Gdisplay,Gxid,Ggc,j,Ly(ag*(Gan[hf-1]+get_real(tvar)*Dgan[hf-1])+bg),k,
       Ly(ag*(Gan[hf]+get_real(tvar)*Dgan[hf])+bg));
  if (Estatistico())
    XDrawLine(Gdisplay,Gxid,Ggc,j,Ly(ag*(Gan[hf-1]-get_real(tvar)*Dgan[hf-1])+bg),k,
	 Ly(ag*(Gan[hf]-get_real(tvar)*Dgan[hf])+bg));
}  /*PlotarTransferencia*/

notify_canvas(PlotarFrequencia)
{
  double dw;
  tiporeffreq *WITH;
  char STR1[20];

  if (!Fpronto) {
    Fdisplay=dpy;
    Fxid=xwin;
    Fgc=DefaultGC(dpy,DefaultScreen(dpy));
    Fpronto=1;
    return;
  }
  if (!analise_valida) return;
  Gdisplay=Fdisplay; Gxid=Fxid; Ggc=Fgc;
  if (!frequencia_valida) ultimof=-1;
  GerarGlobal();
  xv_set(jfrequencia,XV_LABEL,"Frequency Response",NULL);
  yfmax=get_dy(cfrequencia)-tmargin;
  xfmax=get_dx(cfrequencia)-2;
  plotardesvios=(get_sel(ssensi)==0 &&
                 !Adjunto() &&
                 get_sel(ssh)!=2 && /* Restricao temporaria */
		 get_int(tnsaida)==get_int(tsaida));
  ag=(yfmax-ymin)/(get_real(tgmin)-get_real(tgmax));
  bg=yfmax-ag*get_real(tgmin);
  af=(ymin-yfmax)/360.0;
  bf=yfmax+af*180;
  ah=(double)(xfmax-xmin)/get_int(tsegmf);
  bh=xmin;
  /*Tg*/
  ad=(yfmax-ymin)/(get_real(ttgmin)-get_real(ttgmax));
  bd=yfmax-ad*get_real(ttgmin);
  if (get_real(twmin)*get_real(twmax)<=0) set_sel(slog,1);
  if (Log()) {
      dw=Ex(get_real(twmax)/get_real(twmin),1.0/get_int(tsegmf));
      aw=(xfmax-xmin)/log(get_real(twmax)/get_real(twmin));
      bw=xfmax-aw*log(get_real(twmax));
  }
  else {
      dw=(get_real(twmax)-get_real(twmin))/
	   get_int(tsegmf);
      aw=(xfmax-xmin)/(get_real(twmax)-get_real(twmin));
      bw=xfmax-aw*get_real(twmax);
  }
  if (!reter_imagem) {
    IniciarGrafico(cfrequencia,get_real(twmin),get_real(twmax),
		 get_real(tgmin),get_real(tgmax),xfmax,yfmax,
                 Log());
    if (plotardesvios) {
      if (Estatistico())
        XDrawString(Gdisplay,Gxid,Ggc,130,txth,"+stat dev",9);
      else
        XDrawString(Gdisplay,Gxid,Ggc,130,txth,"+det dev",8);
    }
    strcpy(STR1,"dB");
    if (plotarfase) strcat(STR1,",deg");
    if (plotaratraso) strcat(STR1,",s");
    XDrawString(Gdisplay,Gxid,Ggc,xmin+2,ymin+txth,STR1,strlen(STR1));
    XDrawString(Gdisplay,Gxid,Ggc,xfmax-32,yfmax-6,unid[get_sel(srads)],strlen(unid[get_sel(srads)]));
  }
  w=get_real(twmin);
  hf=0;
  fcsr=0;
  colcsr=-100;
  do {
      for (i=1; i<=reffreq; i++) {
          WITH=Reff[i-1];
          fases=WITH->reffases;
          PlotarTransferencia(&WITH->Rnglobal,&WITH->Rden,
                              WITH->Rgan,
			      WITH->Rang,
                              WITH->RTg,
                              LineSolid,cor[6-i],cor[6-i],cor[6-i],
                              WITH->reffreqreter,false,false);
      }
      fases=fasesatual;
      PlotarTransferencia(&Nglobal,&Nden,Gan,Ang,Tg,
                          LineSolid,cor[1],cor[2],cor[4],
			  get_sel(ssh),plotardesvios,false);
      if (Log())
        w*=dw;
      else
        w+=dw;
      hf++;
  } while (hf<=get_int(tsegmf));
  hf=get_int(tsegmf);
  ultimof=hf;
  frequencia_valida=true;
}  /*PlotarFrequencia*/

notify_button(AbrirPlotarFrequencia)
{
   if (AnaliseValida()) {
     open_window(jfrequencia);   
     PlotarFrequencia(cfrequencia,NULL,Fdisplay,Fxid,NULL);
   }
}

notify_button(PlotarEspectro)
{
  double w,nw,ws,na,nb,da,db,ea,eb,ta,tb,t,wt,pa,pb,za,zb,an,ia,ib,ida,idb;
  int xw,nmin,nmax,n,i,j,k,n1,n2,kk;
  boolean listar;
  char STR1[256],STR2[50];

  if (!analise_valida) {
    puts("* No analysis made");
    return;
  }
  if (Adjunto()) return; /*Remover restricao depois*/
  listar=(obj==blsp);
  w=get_real(tsp);
  AbrirPlotarFrequencia(NULL,NULL);
  if (listar) {
    sprintf(STR1,"Output spectrum for %s:\nInput frequency:%*.*f %s",NomeAtual(STR2),cm,dc,w,unid[get_sel(srads)]);
    puts(STR1);
  }
  else XSetLineAttributes(Gdisplay,Ggc,0,LineSolid,CapButt,JoinMiter);
  ws=get_real(tfs);
  if (!Hertz()) ws=2*M_PI*ws;
  n1=(int)((get_real(twmin)+w)/ws);
  n2=(int)((get_real(twmin)-w)/ws);
  if (n1<n2) nmin=n1; else nmin=n2;
  n1=(int)((get_real(twmax)+w)/ws);
  n2=(int)((get_real(twmax)-w)/ws);
  if (n1>n2) nmax=n1; else nmax=n2;
  for (n=nmin; n<=nmax; n++) {
    for (i=0; i<=1; i++) {
      nw=n*ws+(2*i-1)*w;
      if (nw>=get_real(twmin) && nw<=get_real(twmax)) {
        if (Log()) xw=(int)(aw*log(nw)+bw); else xw=(int)(aw*nw+bw);
        wt=(2*i-1)*w/(get_real(tfs));
        if (Hertz()) wt=2*M_PI*wt;
        z1=cos(wt); z2=sin(wt);
        z1f=cos(wt/fases); z2f=sin(wt/fases);
        na=0; nb=0; /* Numerador */
        ia=0; ib=0; /* Entrada nao amostrada */
        ida=0; idb=0; /* Entrada direta */
        for (j=jmin; j<=jmax; j++) { /*Para cada fase da saida*/
          pa=0; pb=0;

          /* Controles das janelas */
          t=-2.0*M_PI*n*(j-1)/fases; /* e^(-jn2pi(j-1)/f) */
          za=cos(t); zb=sin(t);
          t=-2.0*M_PI*n*j/fases;     /* e^(-jn2pij/f) */
          da=cos(t); db=sin(t);

          for (k=kmin; k<=kmax; k++) { /*Para cada fase da entrada*/
            kk=C[j-1][get_int(tsaida)];
            if (kk!=0) {
              Npa[kk-1][k-1].valido=false;
              pa=pa+Nx(&Npa[kk-1][k-1]);
              pb=pb+Ires;

              if (k==j) /* Calcular espectros da entrada */
                if (Nden.g==Npa[kk-1][k-1].g) {
                  an=Npa[kk-1][k-1].cre[Nden.g]; /* Acoplamento instantaneo */
                  /* Acrescenta termos que controlam a posicao das janelas */
                  /* Entrada amostrada */
                  ia=ia+an*da;
                  ib=ib+an*db;
                  /* Entrada direta */
                  if (n==0) ida=ida+an/fases;
                  else {
                    t=an/(2.0*M_PI*n);
                    ida=ida+t*(zb-db);
                    idb=idb-t*(za-da);
                  }
                } 
            }
          }
          /* Acerta a posicao da janela na saida. Adiantada sem amostragem */
          if (get_sel(ssh)==2) na+=Rmult(pa,pb,da,db);
          else na+=Rmult(pa,pb,za,zb);
          nb=nb+Ires;
        }
        Nden.valido=false;
        da=Nx(&Nden); db=Ires;
        if (da==0 || db==0) {
          t=da*da+db*db;
          if (t==0) t=1e-20;
          ea=(na*da+nb*db)/t; eb=(nb*da-na*db)/t;
        }
        else {
          t=da/db+db/da;
          ea=(na/db+nb/da)/t; eb=(nb/db-na/da)/t;
        }
        t=nw/get_real(tfs)/fases;
        if (Hertz()) t=2.0*M_PI*t; 
        switch (get_sel(ssh)) {
          case 0: /* S/H */
            if (t==0) {ta=1/fases; tb=0;}
            else { ta=sin(t)/t/fases; tb=(cos(t)-1)/t/fases;}
            ta=Rmult(ea,eb,ta,tb); tb=Ires;
            break;
          case 1: /* Impulso */
            ta=ea/fases;
            tb=eb/fases;
            break;
          case 2: /* Sem amostragem */
            /* O sinal tem removido o acoplamento direto amostrado,
            e' amostrado e adiantado de 1 fase, e tem somado o
            acoplamento direto continuo */
            if (t==0) {ta=1/fases; tb=0;}
            else {ta=sin(t)/t/fases; tb=(1-cos(t))/t/fases;}
            ta=Rmult(ea-ia,eb-ib,ta,tb)+ida; tb=Ires+idb; 
            break;
        }
        if (ta==0) {
          if (tb==0) tb=1e-11;
          ta=tb*1e-11;
        }
        ModuloFase(ta,tb,&pa,&pb);
        if (listar) {
          sprintf(STR1,"f(%2d,%+d):%9.4f %s %9.4f dB %9.4f deg",n,2*i-1,nw,unid[get_sel(srads)],pa,pb);
          puts(STR1);
        }
        else {
          if (n==0 && i==1) XSetForeground(Gdisplay,Ggc,cor[5]); else XSetForeground(Gdisplay,Ggc,cor[4]);
          kk=Ly(ag*pa+bg);
          XDrawLine(Gdisplay,Gxid,Ggc,xw,yfmax,xw,kk);
          if (kk<yfmax) {
            XSetForeground(Gdisplay,Ggc,cor[6]);
            XFillRectangle(Gdisplay,Gxid,Ggc,xw+1,kk,70l,25);
            XSetForeground(Gdisplay,Ggc,cor[0]);
            sprintf(STR1,"%9.4f",pa);
            XDrawString(Gdisplay,Gxid,Ggc,xw+2,kk+11,STR1,strlen(STR1));
            sprintf(STR1,"%9.4f",pb);
            XDrawString(Gdisplay,Gxid,Ggc,xw+2,kk+23,STR1,strlen(STR1));
          }
        }
      }
    }
  }
}

event_canvas(EventosFrequencia)
{
  static short xi=0, yi=0, xf=0, yf=0;
  static boolean selecao=false;

  double t;
  double TEMP;
  char STR2[256];

  if (!Fpronto) return;
  Gdisplay=Fdisplay; Gxid=Fxid; Ggc=Fgc;
  if (!frequencia_valida) return;
  XSetLineAttributes(Gdisplay,Ggc,0,LineSolid,CapButt,JoinMiter);
  if (selecao) {
    XSetFunction(Gdisplay,Ggc,GXxor); 
    XSetForeground(Gdisplay,Ggc,c_cursor);
    if (event_id(event)==LOC_DRAG) {
      XDrawRectangle(Gdisplay,Gxid,Ggc,xi,yi,xf-xi,yf-yi);
      xf=event_x(event);
      yf=event_y(event);
      XDrawRectangle(Gdisplay,Gxid,Ggc,xi,yi,xf-xi,yf-yi);
      return;
    }
    else {
      selecao=false;
      XDrawRectangle(Gdisplay,Gxid,Ggc,xi,yi,xf-xi,yf-yi);
      if (xi>=xf||yi>=yf) return;
      set_real(twmin,(xi-bw)/aw);
      if (Log())
        set_real(twmin,exp(get_real(twmin)));
      set_real(twmax,(xf-bw)/aw);
      if (Log())
        set_real(twmax,exp(get_real(twmax)));
      set_real(tgmin,(yf-bg)/ag);
      set_real(tgmax,(yi-bg)/ag);
    }
    goto _LRecalcular;
  }
  evento=event_id(event);
  if ((evento>='a') && (evento<='z')) evento=toupper(evento);
  switch (evento) {

    case LOC_DRAG: 
    case MS_MIDDLE:
      fcsr=(short)floor((event_x(event)-bh)/ah+0.5);
      if (fcsr<0)
        fcsr=0;
      if (fcsr>ultimof)
        fcsr=ultimof;
      goto _LCursor;

    case 'L':
      if (Log())
	set_sel(slog,1);
      else
	set_sel(slog,0);
      goto _LRecalcular;

    case 'R':
      if (Log()) {
	TEMP=get_real(twmax)/get_real(twmin);
	set_real(twmax,get_real(twmin)*(TEMP*TEMP));
      }
      else
	set_real(twmax,get_real(twmin)+(get_real(twmax)-get_real(twmin))*2);
	goto _LRecalcular;

    case 'A':
      if (Log())
	set_real(twmax,get_real(twmin)*sqrt(get_real(twmax)/get_real(twmin)));
      else
	set_real(twmax,get_real(twmin)+(get_real(twmax)-get_real(twmin))/2);
      goto _LRecalcular;

    case '>':
    case '.':
      if (Log()) {
	t=sqrt(sqrt(get_real(twmax)/get_real(twmin)));
	set_real(twmin,get_real(twmin)*t);
	set_real(twmax,get_real(twmax)*t);
      }
      else {
	t=(get_real(twmax)-get_real(twmin))/4;
        set_real(twmin,get_real(twmin)+t);
	set_real(twmax,get_real(twmax)+t);
      }
      goto _LRecalcular;

    case '<':
    case ',':
      if (Log()) {
	t=sqrt(sqrt(get_real(twmax)/get_real(twmin)));
        set_real(twmin,get_real(twmin)/t);
	set_real(twmax,get_real(twmax)/t);
      }
      else {
	t=(get_real(twmax)-get_real(twmin))/4;
        set_real(twmin,get_real(twmin)-t);
	set_real(twmax,get_real(twmax)-t);
      }
      goto _LRecalcular;

    case 'G':
      grade=!grade;
      goto _LRetracar;

    case 'F':
      plotarfase=!plotarfase;
      goto _LRetracar;

    case 'T':
      plotaratraso=!plotaratraso;
      goto _LRetracar;

    case 'C':
      goto _LRetracar;

    case 'I':
      goto _LRetracar;

    case 'S':
      if (plotardesvios) {
        w=Frq[fcsr];
        sprintf(STR2,
          "Selected sensitivities dLnT(jw)/dLn(x):\nFrequency:%*.*f %s",
          13,6,w,unid[get_sel(srads)]);
        puts(STR2);
        PlotarTransferencia(&Nglobal,&Nden,Gan,Ang,Tg,
                            LineSolid,cor[1],cor[2],cor[4],
                            get_sel(ssh),plotardesvios,true);
      }
      return;

    case KLEFTARROW:
      if (fcsr>=1)
        fcsr--;
      goto _LCursor;

    case KRIGHTARROW:
      if (fcsr<hf)
        fcsr++;
      goto _LCursor;

    case KUPARROW:
      t=(get_real(tgmax)-get_real(tgmin))/4;
      set_real(tgmin,get_real(tgmin)+t);
      set_real(tgmax,get_real(tgmax)+t);
      goto _LRetracar;

    case KDOWNARROW:
      t=(get_real(tgmax)-get_real(tgmin))/4;
      set_real(tgmin,get_real(tgmin)-t);
      set_real(tgmax,get_real(tgmax)-t);
      goto _LRetracar;

    case '-':
      set_real(tgmax,2*get_real(tgmax)-get_real(tgmin));
      goto _LRetracar;

    case '+':
      set_real(tgmax,(get_real(tgmax)+get_real(tgmin))/2);
      goto _LRetracar;

    case MS_LEFT:
      xi=event_x(event);
      yi=event_y(event);
      xf=xi;
      yf=yi;
      selecao=true;
      return;
    
    case 'E': 
      PlotarEspectro(bpsp,NULL);
      return;

    case 'W':
      PlotarEspectro(blsp,NULL);
      return;

    case 'X':
      reter_imagem=!reter_imagem;
      if (reter_imagem) puts("New plot retains old plot");
      else puts("New plot erases old plot");
      return;
    case 'V':
      k=Ly(ag*Gan[fcsr]+bg);
      if (k<yfmax) {
        XSetForeground(Gdisplay,Ggc,cor[5]);
        XFillRectangle(Gdisplay,Gxid,Ggc,colcsr+1,k,70,13);
        XSetForeground(Gdisplay,Ggc,cor[0]);
        sprintf(txt,"%9.4f",Ex(10,Gan[fcsr]/20));
        XDrawString(Gdisplay,Gxid,Ggc,colcsr+2,k+11,txt,strlen(txt));
      }
      return;
    default:
    return;
  }

_LCursor:
  set_real(tsp,Frq[fcsr]);
  XSetFunction(Gdisplay,Ggc,GXxor); 
  XSetForeground(Gdisplay,Ggc,c_cursor);
  XDrawLine(Gdisplay,Gxid,Ggc,colcsr,ymin,colcsr,yfmax);
  colcsr=(short)floor(fcsr*ah+bh+0.5);
  XDrawLine(Gdisplay,Gxid,Ggc,colcsr,ymin,colcsr,yfmax);
  XSetFunction(Gdisplay,Ggc,GXcopy); 
  XSetForeground(Gdisplay,Ggc,cor[0]);
  XFillRectangle(Gdisplay,Gxid,Ggc,0,0,get_dx(cfrequencia),2*txth+2);
  XSetForeground(Gdisplay,Ggc,cor[1]);
  sprintf(txt,"Fr:%10.4f Ga:%10.4f Ph:%9.4f Tg:%10g",      
    Frq[fcsr],Gan[fcsr],Ang[fcsr],Tg[fcsr]);
  XDrawString(Gdisplay,Gxid,Ggc,1,txth,txt,strlen(txt));
  if (!plotardesvios) return;
  XSetForeground(Gdisplay,Ggc,cor[2]);
  sprintf(txt,"Dg:%10.4f Dp%9.4f",get_real(tvar)*Dgan[fcsr],get_real(tvar)*Dang[fcsr]);
  XDrawString(Gdisplay,Gxid,Ggc,80,2*txth,txt,strlen(txt));
  return;
_LRecalcular:
  frequencia_valida=false;
_LRetracar:
  AbrirPlotarFrequencia(NULL,NULL);
}  /*EventosFrequencia*/

short Limx(double x)
{
  double t;

  t=ax*x+bx;
  if (t>xrmax)
    return xrmax;
  else if (t<xmin)
    return xmin;
  else
    return((short)floor(t+0.5));
}

short Limy(double y)
{
  double t;

  t=ay*y+by;
  if (t>yrmax)
    return yrmax;
  else if (t<ymin)
    return ymin;
  else
    return((short)floor(t+0.5));
}

void PlotarPouZ(raizes *R,boolean xis)
{
  short x,y,i,FORLIM;

  FORLIM=R->g;
  for (i=0; i<FORLIM; i++) {
      x=Limx(R->re[i]);
      y=Limy(R->im[i]);
      if (xis) {
          XDrawLine(Gdisplay,Gxid,Ggc,x-2,y-2,x+2,y+2);
          XDrawLine(Gdisplay,Gxid,Ggc,x-2,y+2,x+2,y-2);
      }
      else
        XDrawArc(Gdisplay,Gxid,Ggc,x-4,y-4,8,8,0,360*64);
        /* circle(x,y,4); */
  }
}

notify_canvas(PlotarRaizes)
{
  double x2,y2;

  if (!Rpronto) {
    Rdisplay=dpy;
    Rxid=xwin;
    Rgc=DefaultGC(dpy,DefaultScreen(dpy));
    Rpronto=1;
    return;
  }
  if (!analise_valida||!(polos_validos||zeros_validos)) {
    puts("* No roots computed");
    return;
  }
  Gdisplay=Rdisplay; Gxid=Rxid; Ggc=Rgc;
  close_window(jpraizes);
  xrmax=get_dx(craizes)-2;
  yrmax=get_dy(craizes)-tmargin;
  xcursor=-2000;
  ycursor=-2000;
  y2=get_real(timmin)+get_real(tdelta);
  ay=(yrmax-ymin)/(get_real(timmin)-y2);
  by=yrmax-ay*get_real(timmin);
  ax=-ay;
  bx=xmin-ax*get_real(tremin);
  x2=(xrmax-bx)/ax;
  IniciarGrafico(craizes,get_real(tremin),x2,get_real(timmin),y2,xrmax,yrmax,false);
  XDrawString(Gdisplay,Gxid,Ggc,xmin+2,ymin+txth,"Im",2);
  XDrawString(Gdisplay,Gxid,Ggc,xrmax-25,yrmax-4,"Re",2);
  XSetForeground(Gdisplay,Ggc,cor[2]);
  XDrawArc(Gdisplay,Gxid,Ggc,(int)floor(bx-ax+0.5),(int)floor(by-ax+0.5),
    2*(int)floor(ax+0.5),2*(int)floor(ax+0.5),0,360*64);
/*
  circle((short)floor(bx+0.5),(short)floor(by+0.5),
         (short)floor(ax+0.5));
*/
  XSetForeground(Gdisplay,Ggc,cor[1]);
  if (polos_validos)
    PlotarPouZ(&Polos,true);
  if (zeros_validos)
    PlotarPouZ(&Zeros,false);
}  /*PlotarRaizes*/

/* variables for EventosRaizes: */
struct LOC_EventosRaizes {

  double x,y,x1,y1,dist;
} ;

void Testar(raizes *R,boolean saopolos,struct LOC_EventosRaizes *LINK)
{
  double teste;
  short j,FORLIM;

  FORLIM=R->g;
  for (j=1; j<=FORLIM; j++) {
      teste=fabs(LINK->x1-R->re[j-1])+fabs(LINK->y1-R->im[j-1]);
      if (teste<LINK->dist) {
          LINK->dist=teste;
          ok=saopolos;
          LINK->x=R->re[j-1];
          LINK->y=R->im[j-1];
          rcsr=j;
      }
  }
}

event_canvas(EventosRaizes)
{
  struct LOC_EventosRaizes V;
  static short xi=0, yi=0, xf=0, yf=0;
  static boolean selecao=false;
  char STR4[256];

  if (!Rpronto) return;
  if (!(polos_validos || zeros_validos)) return;
  Gdisplay=Rdisplay; Gxid=Rxid; Ggc=Rgc;
  if (selecao) {
    XSetFunction(Gdisplay,Ggc,GXxor); 
    XSetForeground(Gdisplay,Ggc,c_cursor);
    if (event_id(event)==LOC_DRAG) {
      XDrawRectangle(Gdisplay,Gxid,Ggc,xi,yi,xf-xi,yf-yi);
      yf=event_y(event);
      xf=xi+(short)floor((yi-yf)*ax/ay+0.5);
      XDrawRectangle(Gdisplay,Gxid,Ggc,xi,yi,xf-xi,yf-yi);
      return;
    }
    else {
      selecao=false;
      XDrawRectangle(Gdisplay,Gxid,Ggc,xi,yi,xf-xi,yf-yi);
      if (xi>=xf||yi>=yf)
        return;
      set_real(tremin,(xi-bx)/ax);
      set_real(timmin,(yf-by)/ay);
      set_real(tdelta,(yi-yf)/ay);
      goto _LReplotar;
    }
  }
  evento=event_id(event);
  if (event_id(event)<='z' && event_id(event)>='a') evento=toupper(evento);
  switch (evento) {

    case LOC_DRAG:
    case MS_MIDDLE:
      V.x1=(event_x(event)-bx)/ax;
      V.y1=(event_y(event)-by)/ay;
      V.dist=1e38;
      if (polos_validos)
      Testar(&Polos,true,&V);
      if (zeros_validos)
      Testar(&Zeros,false,&V);
      XSetForeground(Gdisplay,Ggc,cor[0]);
      XSetFunction(Gdisplay,Ggc,GXcopy);
      XFillRectangle(Gdisplay,Gxid,Ggc,0,0,get_dx(craizes),txth+2);
      XSetForeground(Gdisplay,Ggc,cor[1]);
      if (ok)
        strcpy(STR4,"Pole");
      else
        strcpy(STR4,"Zero");
      sprintf(txt,"%s %hd:%*.*f%*.*fj",STR4,rcsr,8,5,V.x,8,5,V.y);
      XDrawString(Gdisplay,Gxid,Ggc,1,txth,txt,strlen(txt));
      XSetFunction(Gdisplay,Ggc,GXxor); 
      XSetForeground(Gdisplay,Ggc,c_cursor);
      XDrawRectangle(Gdisplay,Gxid,Ggc,xcursor-6,ycursor-6,12,12);
      xcursor=Limx(V.x);
      ycursor=Limy(V.y);
      XDrawRectangle(Gdisplay,Gxid,Ggc,xcursor-6,ycursor-6,12,12);
      return;

    case KUPARROW:
      set_real(timmin,get_real(timmin)+get_real(tdelta)/4);
      break;

    case KDOWNARROW:
      set_real(timmin,get_real(timmin)-get_real(tdelta)/4);
      break;

    case KRIGHTARROW:
      set_real(tremin,get_real(tremin)+get_real(tdelta)/4);
      break;

    case KLEFTARROW:
      set_real(tremin,get_real(tremin)-get_real(tdelta)/4);
      break;

    case '-':
      set_real(timmin,get_real(timmin)-get_real(tdelta)/2);
      set_real(tremin,get_real(tremin)-get_real(tdelta)/2);
      set_real(tdelta,get_real(tdelta)*2);
      break;

    case '+':
      set_real(timmin,get_real(timmin)+get_real(tdelta)/4);
      set_real(tremin,get_real(tremin)+get_real(tdelta)/4);
      set_real(tdelta,get_real(tdelta)/2);
      break;

    case 'G':
      grade=!grade;
      break;

    case MS_LEFT:
      xi=event_x(event);
      yi=event_y(event);
      xf=xi;
      yf=yi;
      selecao=true;
      return;

   default: return;
  }
_LReplotar:
  PlotarRaizes(craizes,NULL,Rdisplay,Rxid,NULL);
}  /*EventosRaizes*/

notify_button(AbrirRaizes)
{
  if (!AnaliseValida())
    return;
  close_window(jpraizes);
  CalcularPoloseZeros();
  open_window(jraizes);
  if (xv_ok)
    PlotarRaizes(craizes,NULL,Rdisplay,Rxid,NULL);
}

notify_button(ListarPoloseZeros)
{
  char STR1[20];

  if (!AnaliseValida())
    return;
  CalcularPoloseZeros();
  if (!polos_validos)
    return;
  ListarRaizes(&Polos,"Denominator");
  if (zeros_validos)
    ListarRaizes(&Zeros,NomeAtual(STR1));
}

double Vin(double t)
{
  switch (get_sel(sinput)) {

    case 0:
      t=1.0;
      break;

    case 1:   /*Usa ht, nao t*/
      if (ht<fases)
        t=1.0;
      else
        t=0.0;
      break;

    case 2:
      t=sin(2*M_PI*get_real(tfreq)*t+get_real(tfase)*M_PI/180);
      break;
  }
  return(t*get_real(tampl));
}

short Lyt(double x)
{
  double t;

  t=av*x+bv;
  if (t>ytmax)
    t=ytmax;
  else if (t<ymin)
    t=ymin;
  return((short)floor(t+0.5));
}

void PlotarSegmento(short i1,short i2,double *X,double *Y,int c)
{
  short i,ia,xn,yn,xa,ya;
  if (i1>0) ia=i1-1; else ia=i1;
  xa=(short)floor(at*X[ia]+bt+0.5); ya=Lyt(Y[ia]);
  XSetForeground(Gdisplay,Ggc,c);
  for (i=i1; i<=i2; i++) {
    xn=(short)floor(at*X[i]+bt+0.5); yn=Lyt(Y[i]);
    XDrawLine(Gdisplay,Gxid,Ggc,xa,ya,xn,yn);
    xa=xn; ya=yn;
  }
}

notify_canvas(PlotarTransiente)
{
  numeradores Num;
  apontadores Q;
  double t,tt,dt,dh,an;
  int p,m,ut0,qq,FORLIM;
  grafico Vid,Vod;
  polpequeno *WITH;
  short FORLIM1;

  if (!Tpronto) {
    Tdisplay=dpy;
    Txid=xwin;
    Tgc=DefaultGC(dpy,DefaultScreen(dpy));
    Tpronto=1;
    return;
  }
  if (!analise_valida) {
      puts("* No analysis made");
      return;
  }
  Gdisplay=Tdisplay; Gxid=Txid; Ggc=Tgc;
  close_window(jptransiente);
  if (Adjunto()) {
      memcpy((char*)Q,(char*)L,sizeof(apontadores));
      memcpy((char*)Num,(char*)Apa,sizeof(numeradores));
  }
  else {
      memcpy((char*)Q,(char*)C,sizeof(apontadores));
      memcpy((char*)Num,(char*)Npa,sizeof(numeradores));
  }
  switch (get_sel(ssh)) {
    case 0: ppf=2; break;
    case 1: ppf=3; break;
    case 2: ppf=get_int(tsegi)+1; break;  
  }
  k=(segmax+1)/ppf-1;
  if (get_int(tsegmt)>k) set_int(tsegmt,k);
  if (get_int(tsegmt)<1) set_int(tsegmt,1);
  ytmax=get_dy(ctransiente)-tmargin;
  xtmax=get_dx(ctransiente)-2;
  av=(ytmax-ymin)/(get_real(tvmin)-get_real(tvmax));
  bv=ytmax-av*get_real(tvmin);
  dt=1/(get_real(tfs)*fases);
  ctcsr=-10;   /*para o cursor*/
  at=(double)(xtmax-xmin)/get_int(tsegmt)/dt;
  bt=xmin;
  IniciarGrafico(ctransiente,0.0,get_int(tsegmt)*dt,
		 get_real(tvmin),get_real(tvmax),xtmax,ytmax,
		 false);
  XDrawString(Gdisplay,Gxid,Ggc,xmin+2,ymin+txth,"Vi,Vo(V)",8);
  XDrawString(Gdisplay,Gxid,Ggc,xtmax-32,ytmax-6,"t(s)",4);
  for (k=0; k<reftran; k++)
    PlotarSegmento(0,Reft[k]->ultimotran,Reft[k]->RTempo, 
                   Reft[k]->RVo,cor[5-k]);
  t=0.0; ht=0; m=Nden.g*fases; tcsr=0; ultimot=-1;
  do {
    p=ht%fases+1;   /*fase atual*/
    tt=0.0;
    /* Adiantando a entrada para tratar acoplamento direto */
    if (get_sel(ssh)==2) Vid[ht]=Vin(t+dt); else Vid[ht]=Vin(t);
    qq=Q[p-1][get_int(tsaida)];
    if (qq!=0 && (get_sel(stiponum)==1 || p==get_int(tfj))) {
      for(k=1; k<=fases; k++) if (get_sel(stiponum)==1 || k==get_int(tfk)) {
        WITH=&Num[qq-1][k-1];
        FORLIM1=WITH->g;
        for (i=0; i<=FORLIM1; i++) {
          j=ht+i*fases-m+WITH->minpot;
	  if (j>=0) tt+=WITH->cre[i]*Vid[j];
        }
      }
      FORLIM=Nden.g;
      for (i=0; i<FORLIM; i++) {
        j=ht+i*fases-m;
        if (j>=0) tt-=Nden.cre[i]*Vod[j];
      }
    }
    Vod[ht]=tt;
    ut0=ultimot+1;
    switch (get_sel(ssh)) {
      case 0:if (ultimot+2<=segmax) {
          for (k=0; k<=1; k++) {
            ultimot++;
            Vi[ultimot]=Vid[ht];
            Vo[ultimot]=Vod[ht];
            Tempo[ultimot]=t+k*dt;
          }
        }
        break;
      case 1:if (ultimot+3<=segmax) {
          ultimot++;
          Vi[ultimot]=Vid[ht];
          Vo[ultimot]=Vod[ht];
          Tempo[ultimot]=t;
          for (k=0; k<=1; k++) {
            ultimot++;
            Vi[ultimot]=Vid[ht];
            Vo[ultimot]=0;
            Tempo[ultimot]=t+k*dt;
          }
        }
        break;
      case 2:if (ultimot+get_int(tsegi)+1<=segmax) {
        /*
        Acoplamento direto:
        Calcula todo o intervalo da fase atual.
        */
        if (qq!=0) {
          WITH=&Num[qq-1][p-1];
          if (Nden.g==WITH->g) an=WITH->cre[WITH->g]; else an=0;
        }
        else an=0;
        for (k=0; k<=get_int(tsegi); k++) {
          dh=(double)k/(double)get_int(tsegi);
          ultimot++;
          tt=(ht+dh)*dt;
          Tempo[ultimot]=tt;
          Vi[ultimot]=Vin(tt);
          Vo[ultimot]=Vod[ht]+an*(Vin(tt)-Vid[ht]);
        }
      }
    }
    if (get_sel(stinput)==0) PlotarSegmento(ut0,ultimot,Tempo,Vi,cor[2]);
    PlotarSegmento(ut0,ultimot,Tempo,Vo,cor[1]);
    t+=dt;
    ht++;
  } while (ht<get_int(tsegmt));
  transiente_valido=TRUE;
}  /*PlotarTransiente*/

notify_button(AbrirTransiente)
{
  if (!AnaliseValida()) return;
  close_window(jptransiente);
  open_window(jtransiente);
  if (xv_ok)
    PlotarTransiente(ctransiente,NULL,Tdisplay,Txid,NULL);
}

event_canvas(EventosTransiente)
{
  double t;

  if (!Tpronto) return;
  if (!transiente_valido) return;
  Gdisplay=Tdisplay; Gxid=Txid; Ggc=Tgc;
  evento=event_id(event);
  if (evento>='a' && evento <='z') evento=toupper(evento);
  switch (evento) {

    case LOC_DRAG:
    case MS_MIDDLE:
      tcsr=(short)floor(((double)event_x(event)-bt)/at*get_real(tfs)*ppf*fases+0.5);
      if (tcsr<0)
        tcsr=0;
      if (tcsr>ultimot)
        tcsr=ultimot;
      goto _LCursor;

    case 'R':
      set_int(tsegmt,get_int(tsegmt)*2);
      goto _LRecalcular;

    case 'A':
      set_int(tsegmt,get_int(tsegmt)/2);
      goto _LRecalcular;

    case KLEFTARROW:
      if (tcsr>=1)
        tcsr--;
      break;

    case KRIGHTARROW:
      if (tcsr<=ultimot-1)
        tcsr++;
      break;

    case KUPARROW:
      t=(get_real(tvmax)-get_real(tvmin))/4;
      set_real(tvmin,get_real(tvmin)+t);
      set_real(tvmax,get_real(tvmax)+t);
      goto _LRetracar;

    case KDOWNARROW:
      t=(get_real(tvmax)-get_real(tvmin))/4;
      set_real(tvmin,get_real(tvmin)-t);
      set_real(tvmax,get_real(tvmax)-t);
      goto _LRetracar;

    case '-':
      set_real(tvmax,2*get_real(tvmax)-get_real(tvmin));
      goto _LRetracar;

    case '+':
      set_real(tvmax,(get_real(tvmax)+get_real(tvmin))/2);
      goto _LRetracar;

    case 'G':
      grade=!grade;
      goto _LRetracar;

    default: return;
  }
_LCursor:
  XSetFunction(Gdisplay,Ggc,GXxor); 
  XSetForeground(Gdisplay,Ggc,c_cursor); 
  XDrawLine(Gdisplay,Gxid,Ggc,ctcsr,ymin,ctcsr,ytmax);
  ctcsr=(short)floor(Tempo[tcsr]*at+bt);
  XDrawLine(Gdisplay,Gxid,Ggc,ctcsr,ymin,ctcsr,ytmax);
  XSetFunction(Gdisplay,Ggc,GXcopy); 
  XSetForeground(Gdisplay,Ggc,cor[0]);
  XFillRectangle(Gdisplay,Gxid,Ggc,0,0,get_dx(ctransiente),txth+2);
  XSetForeground(Gdisplay,Ggc,cor[1]);
  sprintf(txt,"t:%9.5fp:%hd Vo:%8.5f Vi:%8.5f",Tempo[tcsr],(tcsr/ppf)%fases+1,Vo[tcsr],Vi[tcsr]);
  XDrawString(Gdisplay,Gxid,Ggc,1,txth,txt,strlen(txt));
  return;
_LRecalcular:
  transiente_valido=false;
_LRetracar:
  PlotarTransiente(ctransiente,NULL,Tdisplay,Txid,NULL);
}  /*EventosTransiente*/

void AbrirJNetlist(Xv_opaque obj)
{
  /*open_window(jdiretorio);*/
  open_window(jnetlist);
}

notify_menu(TratarMenu1)
{
  char STR1[256];

  switch (get_item(obj)) {

    case 1:
      AbrirJNetlist(NULL);
      break;

    case 2:
      open_window(jpanalise);
      break;

    case 3:
      ListarDenominador();
      break;

    case 4:
      open_window(jpnumerador);
      break;

    case 5:
      open_window(jpraizes);
      break;

    case 6:
      open_window(jpfrequencia);
      break;

    case 7:
      open_window(jptransiente);
      break;

    case 8:
      sprintf(STR1,"ASIZ - version %s",versao);
      puts(STR1);
      puts("Z-domain analysis of switched-current filters");
      puts("By: Antonio Carlos Moreirao de Queiroz");
      puts("COPPE/EE\nUniversidade Federal do Rio de Janeiro");
      puts("CP 68504\nCEP 21945-970, Rio de Janeiro, RJ, Brasil");
      puts("e-mail: acmq@coe.ufrj.br");
      break;

    case 9:
      open_window(jmos);
      break;

    case 10:
      if (get_int(tnsaida)!=get_int(tsaida))
        puts("* Deviations not available for the current output node");
      else if (get_sel(ssh)==2)
        puts("* Sensitivity analysis for unsampled input not implemented");
      else {
        open_window(jsensi);
        /* Isto nao deveria ser necessario */
        PlotarSensi(csensi,NULL,Sdisplay,Sxid,NULL);
        } 
      break;

    case 11:
      open_window(jpespectro);
      break;

    case 12:
      notify_stop();
      break;
  }
}

notify_button(ListarNumerador)
{
  char STR1[256];
  char STR2[256],STR3[256];

  if (!AnaliseValida())
    return;
  switch (get_sel(stiponum)) {

    case 0:
      sprintf(STR3,"Partial numerator %s:",NomeAtual(STR1));
      puts(STR3);
      if (Adjunto()) {
	  k=L[get_int(tfj)-1][get_int(tsaida)];
          if (k!=0)
	    ListarPequeno(&Apa[k-1][get_int(tfk)-1]);
          else
            puts("Zero");
      }
      else {
	  k=C[get_int(tfj)-1][get_int(tsaida)];
          if (k!=0)
	    ListarPequeno(&Npa[k-1][get_int(tfk)-1]);
          else
            puts("Zero");
      }
      break;

    case 1:
      sprintf(STR2,"Global numerator %s:",NomeAtual(STR1));
      puts(STR2);
      GerarGlobal();
      ListarGrande();
      break;
  }
}

notify_menu(TratarMenuPlot)
{
  tiporeffreq *WITH;
  char STR2[256],STR3[256];
  tiporeftran *WITH1;
  char STR5[82];

  switch (get_item(obj)) {

    case 1:
      if (obj==menuf) {
	  if (frequencia_valida) {
	      if (reffreq<refmax) {
                if ((Reff[reffreq]=(tiporeffreq*)malloc(sizeof(tiporeffreq)))!=0) {
		  reffreq++;
		  WITH=Reff[reffreq-1];
		  WITH->Rnglobal=Nglobal;
		  WITH->Rden=Nden;
                  if ((WITH->Rden.cre=(double*)malloc(sizepoly))!=0) {
                    memcpy(WITH->Rden.cre,Nden.cre,sizepoly);
                    WITH->reffases=fases;
		    memcpy(WITH->Rgan,Gan,sizeof(grafico));
		    memcpy(WITH->Rang,Ang,sizeof(grafico));
                    memcpy(WITH->RTg,Tg,sizeof(grafico));
		    WITH->reffreqreter=get_sel(ssh);
		    sprintf(STR3,"Frequency response reference #%hd saved",reffreq);
		    puts(STR3);
                  }
                  else {
                    reffreq--;
                    free((char*)Reff[reffreq]);
                    puts("* Not enough memory");
                  }
		}
		else
		  puts("* Not enough memory");
	     }
	     else
	       puts("* Too many references");
	  }
	  else
	    puts("* Nothing to save");
      }
      else if (obj==menut) {
	  if (transiente_valido) {
	      if (reftran<refmax) {
		if ((Reft[reftran]=(tiporeftran*)malloc(sizeof(tiporeftran)))!=0) {
		  reftran++;
		  WITH1=Reft[reftran-1];
		  memcpy((char*)WITH1->RVo,(char*)Vo,sizeof(grafico));
                  memcpy((char*)WITH1->RTempo,(char*)Tempo, sizeof(grafico));
		  WITH1->ultimotran=ultimot;
		  sprintf(STR2,"Transient response reference #%hd saved",
			  reftran);
		  puts(STR2);
		}
		else
		  puts(" Not enough memory");
	      }
	      else
		puts("* Too many references");
	  }
	  else
	    puts("* Nothing to save");
      }
      else
	puts("* Root references are not implemented");
      break;

    case 2:
      if (obj==menuf) {
          if (reffreq>0) {
              free((char*)Reff[reffreq-1]->Rden.cre);
	      free((char*)Reff[reffreq-1]);
	      free((char*)Reff[reffreq-1]);
	      reffreq--;
	      AbrirPlotarFrequencia(NULL,NULL);
	      sprintf(STR3,"Frequency response reference #%hd eliminated",reffreq+1);
	      puts(STR3);
	  }
	  else
	    puts("* No reference saved");
      }
      else if (obj==menut) {
          if (reftran>0) {
              free((char*)Reft[reftran-1]);
              reftran--;
              PlotarTransiente(ctransiente,NULL,Tdisplay,Txid,NULL);
	      sprintf(STR2,"Transient response reference #%hd eliminated",reftran+1);
              puts(STR2);
          }
          else
            puts("* No reference saved");
      }
      else
        puts("* Root references are not implemented");
      break;

    case 3:
      if (obj==menuf) {
          if (frequencia_valida) {
              if (relatorio)
		EscreverTabelaFrequencia();
              else
                AbrirJRelatorio(frequencia);
          }
          else
            puts("* Nothing to save");
      }
      else if (obj==menut) {
          if (transiente_valido) {
              if (relatorio)
                EscreverTabelaTransiente();
              else
                AbrirJRelatorio(transiente);
          }
          else
            puts("* Nothing to save");
      }
      break;
     
    case 4:
      if (relatorio) {
          fclose(arquivo);
	  sprintf(STR5,"Report file %s closed",get_text(trelatorio));
          puts(STR5);
          relatorio=false;
      }
      else
        puts("* No report file open");
      break;

    case 5:
      if (obj==menuf)
        open_window(jpfrequencia);
      else if (obj==menut)
        open_window(jptransiente);
      else
	open_window(jpraizes);
      break;
  }
}

notify_textfield(SetarSaida)
{
  set_int(tsaida,get_int(tnsaida));
  InvalidarAnalise(NULL,NULL);
  return PANEL_NEXT;
}

notify_button(AbrirRelatorio)
{
  time_t t;
  close_window(jrelatorio);
  arquivo=fopen(get_text(trelatorio),"w");
  time(&t);
  ioresult=fprintf(arquivo,"ASIZ *====* Version %s *====* %s",
	   versao,ctime(&t));
  ioresult=fprintf(arquivo,"\nTitle: %s\n",rede);
  ioresult=fprintf(arquivo,"\nNodes: %hd; Phases: %hd\n",nos,fases);
  relatorio=(ioresult!=EOF);
  if (!relatorio) {
    Falha();
    return;
  }
  switch (asalvar) {

    case frequencia:
      EscreverTabelaFrequencia();
      break;

    case transiente:
      EscreverTabelaTransiente();
      break;
  }
}

notify_button(LerGrupos)
{
  char STR1[256],STR2[256];
  _REC_NetList *WITH;
  char *TEMP;
  FILE *arquivo;

  if (!netlist_valido) return;
  sprintf(STR1,"%s%s",rede,sg);
  arquivo=fopen(STR1,"r");
  if (arquivo==0) {
      sprintf(STR2,"* File %s%s not found",rede,sg);
      puts(STR2);
      return;
  }
  e=0;
  ok=true;
  while (e<elementos&&ok) {
      e++;
      WITH=&NetList[e-1];
      WITH->grupo=getc(arquivo);
      ch=getc(arquivo);
      fgets(txt,256,arquivo);
      TEMP=strchr(txt,'\n');
      if (TEMP!=NULL)
	*TEMP=0;
      WITH->selecionado=(ch=='+');
      ok=(strcmp(txt,WITH->nome)==0);
  }
  if (ok) {
      sprintf(STR2,"Selection read from file %s%s",rede,sg);
      puts(STR2);
  }
  else {
      sprintf(STR2,"* The file %s%s does not correspond to the netlist",
	      rede,sg);
      puts(STR2);
  }
  fclose(arquivo);
  PlotarSensi(csensi,NULL,Sdisplay,Sxid,NULL);
  frequencia_valida=false;
}

notify_button(EscreverGrupos)
{
/* !!! Notar que as operacoes com arquivo nao sao testadas */
  char STR1[256],STR2[256];
  _REC_NetList *WITH;
  FILE *arquivo;

  if (!netlist_valido) return;
  sprintf(STR1,"%s%s",rede,sg);
  arquivo=fopen(STR1,"w");
  for (e=1; e<=elementos; e++) {
      WITH=&NetList[e-1];
      if (WITH->selecionado)
	ch='+';
      else
	ch='-';
      fprintf(arquivo,"%c%c%s\n",WITH->grupo,ch,WITH->nome);
  }
  fclose(arquivo);
  sprintf(STR2,"Selection saved on file %s%s",rede,sg);
  puts(STR2);
}

void main(int argc,char *argv[])
{
  char *helppath, buf[BUFSIZ];

  printf("\nASIZ, Version %s\nBy Antonio Carlos M. de Queiroz\n",versao);
  strcpy(buf,"HELPPATH=/usr/lib/help:.:");
  if ((helppath=getenv("HELPPATH"))!=0) strcat(buf,helppath);
  putenv(buf);
  arquivo=NULL;
  normal=true;
  plotarfase=true;
  plotaratraso=true;
  reffreq=0;
  reftran=0;
  relatorio=false;
  Frq=(double*)malloc(sizeof(grafico));
  Gan=(double*)malloc(sizeof(grafico));
  Ang=(double*)malloc(sizeof(grafico));
  Tg=(double*)malloc(sizeof(grafico));
  Tempo=(double*)malloc(sizeof(grafico));
  Vi=(double*)malloc(sizeof(grafico));
  Vo=(double*)malloc(sizeof(grafico));
  Dgan=(double*)malloc(sizeof(grafico));
  assert((Dang=(double*)malloc(sizeof(grafico)))!=0);
  xv_init(XV_INIT_ARGC_PTR_ARGV,&argc,argv,NULL);
  menu1=xv_create(NULL,MENU,
    MENU_TITLE_ITEM,"Main menu:",
    MENU_STRINGS,"netlist","analysis","denominator",
      "numerator","poles and zeros","frequency response",
      "transient response","informations",
      "mosfet parameters","sensitivity","output spectrum",
      "quit",
    NULL,
    MENU_NOTIFY_PROC,TratarMenu1,
    NULL);
  menuf=xv_create(NULL,MENU,
    MENU_TITLE_ITEM,"Plot menu:",
    MENU_STRINGS,"save as reference","delete reference","save in report file",
      "close report file","parameters",
    NULL,
    MENU_NOTIFY_PROC,TratarMenuPlot,
    NULL);
  menut=xv_create(NULL,MENU,
    MENU_TITLE_ITEM,"Plot menu:",
    MENU_STRINGS,"save as reference","delete reference","save in report file",
      "close report file","parameters",
    NULL,
    MENU_NOTIFY_PROC,TratarMenuPlot,
    NULL);
  menur=xv_create(NULL,MENU,
    MENU_TITLE_ITEM,"Plot menu:",
    MENU_STRINGS,"save as reference","delete reference","save in report file",
      "close report file","parameters",
    NULL,
    MENU_NOTIFY_PROC,TratarMenuPlot,
    NULL);
 
  jfrequencia=xv_create(NULL,FRAME,
    XV_X,0,
    XV_Y,0,
    XV_WIDTH,639,
    XV_HEIGHT,479,
    XV_LABEL,"ASIZ",
    FRAME_NO_CONFIRM,FALSE,
    NULL);
  closed_image=(Server_image)xv_create(NULL,SERVER_IMAGE,
    XV_WIDTH,64,
    XV_HEIGHT,64,
    SERVER_IMAGE_BITS,closed_bits,
    NULL);
  icon=(Icon)xv_create(jfrequencia,ICON,
    ICON_IMAGE,closed_image,
    XV_X,100,
    XV_Y,100,
    NULL);
  xv_set(jfrequencia,FRAME_ICON,icon,NULL);  

  {Display *dpy=(Display*)xv_get(jfrequencia,XV_DISPLAY); 
    if (DefaultDepth(dpy,DefaultScreen(dpy))>1)
      cms=xv_create(NULL,CMS,
        CMS_TYPE, XV_STATIC_CMS,
        CMS_SIZE,7,
        CMS_NAMED_COLORS, "white","black","blue","red","green","orange","gray",NULL,
        NULL);
    else {
      printf("Black and white mode\n");
      cms=xv_create(NULL,CMS,
        CMS_SIZE,7,
        CMS_TYPE, XV_STATIC_CMS,
        CMS_NAMED_COLORS, "white","black","black","black","black","black","black",NULL,
        NULL);
    }
    cor=(unsigned long *)xv_get(cms,CMS_INDEX_TABLE);
  }
  if (cms==NULL) printf("Problems in colormap segment creation\n");
  c_cursor=cor[0]^cor[3];
    
  panel=(Panel)xv_create(jfrequencia,PANEL,
    XV_X,0,
    XV_Y,0,
    XV_WIDTH,WIN_EXTEND_TO_EDGE,
    XV_HEIGHT,30,
    PANEL_LAYOUT,PANEL_HORIZONTAL,
    NULL);
  xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"General",
    PANEL_ITEM_MENU,menu1,
    XV_HELP_DATA,"asiz:bgeneral",
    NULL);
  xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Local",
    PANEL_ITEM_MENU,menuf,
    XV_X,90,
    XV_HELP_DATA,"asiz:bmenul",
    NULL);
  cfrequencia=xv_create(jfrequencia,CANVAS,
    XV_Y,30,
    WIN_CMS,cms,
    CANVAS_X_PAINT_WINDOW,TRUE,
    CANVAS_REPAINT_PROC,PlotarFrequencia,
    XV_HELP_DATA,"asiz:cfrequencia",
    NULL);

  xv_set(canvas_paint_window(cfrequencia),
    WIN_EVENT_PROC,EventosFrequencia,
    WIN_CONSUME_EVENTS,
      WIN_ASCII_EVENTS, LOC_DRAG, LOC_MOVE, WIN_MOUSE_BUTTONS,
      WIN_TOP_KEYS, WIN_META_EVENTS,
      NULL,
    WIN_IGNORE_EVENTS, WIN_UP_EVENTS, WIN_UP_ASCII_EVENTS,
      NULL,
    NULL);

  jraizes=xv_create(jfrequencia,FRAME,
    XV_LABEL,"Poles and Zeros",
    XV_X,100,
    XV_Y,100,
    XV_WIDTH,400,
    XV_HEIGHT,400,
    NULL);
  panel=(Panel)xv_create(jraizes,PANEL,
    XV_X,0,
    XV_Y,0,
    XV_WIDTH,WIN_EXTEND_TO_EDGE,
    XV_HEIGHT,30,
    PANEL_LAYOUT,PANEL_HORIZONTAL,
    NULL);
  xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Local",
    PANEL_ITEM_MENU,menur,
    XV_HELP_DATA,"asiz:bmenul",
    NULL);
  craizes=xv_create(jraizes,CANVAS,
    WIN_CMS,cms,
    CANVAS_X_PAINT_WINDOW,TRUE,
    CANVAS_REPAINT_PROC,PlotarRaizes,
    XV_Y,30,
    XV_HELP_DATA,"asiz:craizes",
    NULL);

  xv_set(canvas_paint_window(craizes),
    WIN_EVENT_PROC,EventosRaizes,
    WIN_CONSUME_EVENTS,
      WIN_ASCII_EVENTS, LOC_DRAG, LOC_MOVE, WIN_MOUSE_BUTTONS,
      WIN_TOP_KEYS, WIN_META_EVENTS,
      NULL,
    WIN_IGNORE_EVENTS, WIN_UP_EVENTS, WIN_UP_ASCII_EVENTS,
      NULL,
    NULL);

  jtransiente=xv_create(jfrequencia,FRAME,
    XV_WIDTH,400,
    XV_HEIGHT,400,
    XV_LABEL,"Transient Response",
    XV_X,200,
    XV_Y,200,
    NULL);
  panel=(Panel)xv_create(jtransiente,PANEL,
    XV_X,0,
    XV_Y,0,
    XV_WIDTH,WIN_EXTEND_TO_EDGE,
    XV_HEIGHT,30,
    PANEL_LAYOUT,PANEL_HORIZONTAL,
    NULL);
  xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Local",
    PANEL_ITEM_MENU,menut,
    XV_HELP_DATA,"asiz:bmenul",
    NULL);
  ctransiente=xv_create(jtransiente,CANVAS,
    WIN_CMS,cms,
    CANVAS_X_PAINT_WINDOW,TRUE,
    CANVAS_REPAINT_PROC,PlotarTransiente,
    XV_Y,30,
    XV_HELP_DATA,"asiz:ctransiente",
    NULL);

  xv_set(canvas_paint_window(ctransiente),
    WIN_EVENT_PROC,EventosTransiente,
    WIN_CONSUME_EVENTS,
      WIN_ASCII_EVENTS, LOC_DRAG, LOC_MOVE, WIN_MOUSE_BUTTONS,
      WIN_TOP_KEYS, WIN_META_EVENTS,
      NULL,
    WIN_IGNORE_EVENTS, WIN_UP_EVENTS, WIN_UP_ASCII_EVENTS,
      NULL,
    NULL);

  jpfrequencia=xv_create(jfrequencia,FRAME_CMD,
    XV_X,100,
    XV_Y,200,
    XV_LABEL,"Frequency Response Parameters",
    NULL);
  panel=(Panel)xv_get(jpfrequencia,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  twmin=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Minimum frequency",
    PANEL_VALUE,"0.2",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_NOTIFY_PROC,InvalidarFrequencia,
    XV_HELP_DATA,"asiz:twmin",
    NULL);
  twmax=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Maximum frequency",
    PANEL_VALUE,"5.0",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_NOTIFY_PROC,InvalidarFrequencia,
    XV_HELP_DATA,"asiz:twmin",
    NULL);
  tgmin=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Minimum gain",
    PANEL_VALUE,"-80.0",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    XV_HELP_DATA,"asiz:tgmin",
    NULL);
  tgmax=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Maximum gain",
    PANEL_VALUE,"10.0",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    XV_HELP_DATA,"asiz:tgmin",
    NULL);
  ttgmin=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Minimum delay",
    PANEL_VALUE,"-10.0",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    XV_HELP_DATA,"asiz:ttgmin",
    NULL);
  ttgmax=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Maximum delay",
    PANEL_VALUE,"30.0",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    XV_HELP_DATA,"asiz:ttgmin",
    NULL);
  slog=xv_create(panel,PANEL_CHOICE,
    PANEL_CHOICE_STRINGS,"log","linear",NULL,
    PANEL_LABEL_STRING,"Scale",
    PANEL_VALUE,0,
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_NOTIFY_PROC,InvalidarFrequencia,
    XV_HELP_DATA,"asiz:slog",
    NULL);
  srads=xv_create(panel,PANEL_CHOICE,
    PANEL_CHOICE_STRINGS,"rad/s","Hertz",NULL,
    PANEL_LABEL_STRING,"Frequency unit",
    PANEL_VALUE,0,
    PANEL_NOTIFY_PROC,InvalidarFrequencia,
    NULL);
  tsegmf=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Segments",
    PANEL_VALUE,200,
    PANEL_MIN_VALUE,1,
    PANEL_MAX_VALUE,segmax,
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_NOTIFY_PROC,InvalidarFrequencia,
    XV_HELP_DATA,"asiz:tsegmf",
    NULL);
  brf=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Plot",
    PANEL_NOTIFY_PROC,AbrirPlotarFrequencia,
    NULL);
  window_fit(panel);
  window_fit(jpfrequencia);

  jpespectro=xv_create(jfrequencia,FRAME_CMD,
    XV_X,150,
    XV_Y,150,
    XV_LABEL,"Output Spectrum Parameters",
    NULL);
  panel=(Panel)xv_get(jpespectro,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  tsp=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Input frequency",
    PANEL_VALUE,"1.0",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    XV_HELP_DATA,"asiz:tsp",
    NULL);
  bpsp=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Plot",
    PANEL_NOTIFY_PROC,PlotarEspectro,
    NULL);
  blsp=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"List",
    PANEL_NOTIFY_PROC,PlotarEspectro,
    NULL);
  window_fit(panel);
  window_fit(jpespectro);

  jptransiente=xv_create(jfrequencia,FRAME_CMD,
    XV_X,300,
    XV_Y,400,
    XV_LABEL,"Transient Response Parameters",
    NULL);
  panel=(Panel)xv_get(jptransiente,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  tvmin=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Minimum voltage",
    PANEL_VALUE,"-1.0",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    NULL);
  tvmax=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Maximum voltage",
    PANEL_VALUE,"3.0",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    NULL);
  tsegmt=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Phase steps",
    PANEL_VALUE,100,
    PANEL_MIN_VALUE,1,
    PANEL_VALUE_DISPLAY_LENGTH,7,
    PANEL_MAX_VALUE,segmax,
    PANEL_NOTIFY_PROC,InvalidarTransiente,
    XV_HELP_DATA,"asiz:tsegmt",
    NULL);
  tsegi=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Segments/phase",
    PANEL_VALUE,3,
    PANEL_MIN_VALUE,1,
    PANEL_VALUE_DISPLAY_LENGTH,4,
    PANEL_MAX_VALUE,segmax,
    PANEL_NOTIFY_PROC,InvalidarTransiente,
    XV_HELP_DATA,"asiz:tsegi",
    NULL);
  sinput=xv_create(panel,PANEL_CHOICE,
    PANEL_CHOICE_STRINGS,"step","impulse","sinusoid",NULL,
    PANEL_LABEL_STRING,"Input",
    PANEL_VALUE,0,
    PANEL_NOTIFY_PROC,InvalidarTransiente,
    XV_HELP_DATA,"asiz:sinput",
    NULL);
  stinput=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Plot input",
    PANEL_CHOICE_STRINGS,"yes","no",NULL,
    PANEL_VALUE,0,
    NULL);
  tampl=xv_create(panel,PANEL_TEXT,
    PANEL_VALUE,"1.0",
    PANEL_LABEL_STRING,"Amplitude (A)",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_NOTIFY_PROC,InvalidarTransiente,
    NULL);
  tfreq=xv_create(panel,PANEL_TEXT,
    PANEL_VALUE,"0.1",
    PANEL_LABEL_STRING,"Sin freq. (Hz)",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_NOTIFY_PROC,InvalidarTransiente,
    NULL);
  tfase=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Sin phase",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_NOTIFY_PROC,InvalidarTransiente,
    PANEL_VALUE,"0",
    NULL);
  brt=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Plot",
    PANEL_NOTIFY_PROC,AbrirTransiente,
    NULL);
  window_fit(panel);
  window_fit(jptransiente);

  jpraizes=xv_create(jfrequencia,FRAME_CMD,
    XV_LABEL,"Poles and Zeros Parameters",
    XV_X,200,
    XV_Y,300,
    NULL);
  panel=(Panel)xv_get(jpraizes,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  ttolz=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Error tolerance",
    PANEL_VALUE,"1e-11",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_NOTIFY_PROC,InvalidarRaizes,
    XV_HELP_DATA,"asiz:ttolz",
    NULL);
  ttolp=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Magnitude tol. ",
    PANEL_VALUE,"1e-11",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_NOTIFY_PROC,InvalidarRaizes,
    XV_HELP_DATA,"asiz:ttolp",
    NULL);
  treal=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Real approx.",
    PANEL_VALUE,"0.9",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_NOTIFY_PROC,InvalidarRaizes,
    XV_HELP_DATA,"asiz:timag",
    NULL);
  timag=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Imag approx.",
    PANEL_VALUE,"0.1",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    PANEL_NOTIFY_PROC,InvalidarRaizes,
    XV_HELP_DATA,"asiz:timag",
    NULL);
  tremin=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Plot real minimum",
    PANEL_VALUE,"-2.0",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    XV_HELP_DATA,"asiz:tremin",
    NULL);
  timmin=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Plot imag minimum",
    PANEL_VALUE,"-2.0",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    XV_HELP_DATA,"asiz:tremin",
    NULL);
  tdelta=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Plot height",
    PANEL_VALUE,"4.0",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    XV_HELP_DATA,"asiz:tdelta",
    NULL);
  blist=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"List",
    PANEL_NOTIFY_PROC,ListarPoloseZeros,
    XV_HELP_DATA,"asiz:blist",
    NULL);
  bplot=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Plot",
    PANEL_NOTIFY_PROC,AbrirRaizes,
    XV_HELP_DATA,"asiz:bplot",
    NULL);
  window_fit(panel);
  window_fit(jpraizes);

  jnetlist=xv_create(jfrequencia,FRAME_CMD,
    XV_LABEL,"Netlist File",
    XV_Y,65,
    XV_X,10,
    NULL);
  panel=(Panel)xv_get(jnetlist,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  tnetlist=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Filename",
    PANEL_VALUE_DISPLAY_LENGTH,21,
    XV_HELP_DATA,"asiz:tnetlist",
    NULL);
  if (argc>1) {
    strcpy(get_text(tnetlist),argv[1]);
  }
  tfases=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Number of phases",
    PANEL_VALUE,2,
    PANEL_MIN_VALUE,1,
    PANEL_MAX_VALUE,fasmax,
    PANEL_VALUE_DISPLAY_LENGTH,7,
    XV_HELP_DATA,"asiz:tfases",
    NULL);
  bread=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Read",
    PANEL_NOTIFY_PROC,LerNetList,
    NULL);
  window_fit(panel);
  window_fit(jnetlist);

  jpanalise=xv_create(jfrequencia,FRAME_CMD,
    XV_LABEL,"Analysis and Sampling Parameters",
    XV_X,10,
    XV_Y,100,
    NULL);
  panel=(Panel)xv_get(jpanalise,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  tnsaida=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Output node for sensitivity",
    PANEL_VALUE_DISPLAY_LENGTH,7,
    PANEL_VALUE,1,
    PANEL_NOTIFY_PROC,SetarSaida,
    XV_HELP_DATA,"asiz:tnsaida",
    NULL);
  traio=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Interpolation circle radius",
    PANEL_VALUE,"1.1",
    PANEL_VALUE_DISPLAY_LENGTH,7,
    PANEL_NOTIFY_PROC,InvalidarAnalise,
    XV_HELP_DATA,"asiz:traio",
    NULL);
  tdisp=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Polynomial dispersion factor",
    PANEL_VALUE,"1e6",
    PANEL_VALUE_DISPLAY_LENGTH,7,
    PANEL_NOTIFY_PROC,InvalidarAnalise,
    XV_HELP_DATA,"asiz:tdisp",
    NULL);
  tminimo=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Minimum non zero value",
    PANEL_VALUE,"1e-10",
    PANEL_VALUE_DISPLAY_LENGTH,7,
    PANEL_NOTIFY_PROC,InvalidarAnalise,
    XV_HELP_DATA,"asiz:tminimo",
    NULL);
  tgrau=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Estimated complexity order",
    PANEL_MIN_VALUE,0,
    PANEL_VALUE_DISPLAY_LENGTH,7,
    PANEL_NOTIFY_PROC,InvalidarAnalise,
    XV_HELP_DATA,"asiz:tgrau",
    NULL);
  tfs=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Sampling frequency (Hz)",
    PANEL_VALUE,"1.0",
    PANEL_VALUE_DISPLAY_LENGTH,13,
    PANEL_NOTIFY_PROC,InvalidarFrequencia,
    XV_HELP_DATA,"asiz:tfs",
    NULL);
  ssh=xv_create(panel,PANEL_CHOICE,
    PANEL_CHOICE_STRINGS,"S/H","Impulse","None",NULL,
    PANEL_LABEL_STRING,"Output sampling",
    PANEL_VALUE,0,
    PANEL_NOTIFY_PROC,InvalidarFrequencia,
    XV_HELP_DATA,"asiz:ssh",
    NULL);
  banalisar=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Analyze",
    PANEL_NOTIFY_PROC,AnalisarCircuito,
    XV_HELP_DATA,"asiz:banalisar",
    NULL);
  ganalise=xv_create(panel,PANEL_GAUGE,
    PANEL_LABEL_STRING,"Analysis",
    PANEL_MIN_VALUE,0,
    PANEL_MAX_VALUE,100,
    XV_HELP_DATA,"asiz:ganalise",
    NULL);
  window_fit(panel);
  window_fit(jpanalise);

  jpnumerador=xv_create(jfrequencia,FRAME_CMD,
    XV_LABEL,"Numerator Parameters",
    XV_X,10,
    XV_Y,100,
    NULL);
  panel=(Panel)xv_get(jpnumerador,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  tsaida=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Output node",
    PANEL_MIN_VALUE,1,   /*PANEL_MAX_VALUE setado em LerNetList*/
    PANEL_VALUE,1,
    PANEL_VALUE_DISPLAY_LENGTH,7,
    PANEL_NOTIFY_PROC,InvalidarNumerador,
    XV_HELP_DATA,"asiz:tsaida",
    NULL);
  stiponum=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Type",
    PANEL_CHOICE_STRINGS,"Partial","Global",NULL,
    PANEL_VALUE,1,
    PANEL_NOTIFY_PROC,InvalidarNumerador,
    XV_HELP_DATA,"asiz:stiponum",
    NULL);
  tfk=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Partial numerator input phase ",
    PANEL_MIN_VALUE,1,   /*Maximo setado por LerNetList*/
    PANEL_VALUE,1,
    PANEL_VALUE_DISPLAY_LENGTH,7,
    PANEL_NOTIFY_PROC,InvalidarNumerador,
    XV_HELP_DATA,"asiz:tfk",
    NULL);
  tfj=xv_create(panel,PANEL_NUMERIC_TEXT,
    PANEL_LABEL_STRING,"Partial numerator output phase",
    PANEL_MIN_VALUE,1,   /*Idem*/
    PANEL_VALUE,1,
    PANEL_VALUE_DISPLAY_LENGTH,7,
    PANEL_NOTIFY_PROC,InvalidarNumerador,
    XV_HELP_DATA,"asiz:tfk",
    NULL);
  sadjunto=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Network",
    PANEL_CHOICE_STRINGS,"normal","adjoint",NULL,
    PANEL_VALUE,0,
    PANEL_NOTIFY_PROC,InvalidarNumerador,
    XV_HELP_DATA,"asiz:sadjunto",
    NULL);
  blistnum=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"List",
    PANEL_NOTIFY_PROC,ListarNumerador,
    XV_HELP_DATA,"asiz:blistnum",
    NULL);
  window_fit(panel);
  window_fit(jpnumerador);

  jsensi=xv_create(jfrequencia,FRAME,
    XV_LABEL,"Sensitivity Analysis Parameters",
    XV_WIDTH,400,
    XV_HEIGHT,400,
    XV_X,300,
    XV_Y,300,
    NULL);
  panel=xv_create(jsensi,PANEL,
    XV_X,0,
    XV_Y,0,
    XV_WIDTH,WIN_EXTEND_TO_EDGE,
    XV_HEIGHT,90,
    NULL);
  ssensi=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Do sensitivity analysis",
    PANEL_CHOICE_STRINGS,"yes","no",NULL,
    PANEL_VALUE,1,
    PANEL_NOTIFY_PROC,InvalidarDesvios,
    XV_HELP_DATA,"asiz:ssensi",
    NULL);
  sdesvios=xv_create(panel,PANEL_CHOICE,
    PANEL_CHOICE_STRINGS,"statistic","deterministic",NULL,
    PANEL_LABEL_STRING,"Deviation",
    PANEL_VALUE,0,
    XV_Y,30,
    XV_X,0,
    PANEL_NOTIFY_PROC,InvalidarFrequencia,
    XV_HELP_DATA,"asiz:sdesvios",
    NULL);
  tvar=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Variability",
    PANEL_VALUE,"0.05",
    PANEL_VALUE_DISPLAY_LENGTH,20,
    XV_Y,60,
    XV_X,0,
    XV_HELP_DATA,"asiz:tvar", 
    NULL);
  brsensi=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Read",
    XV_X,250,XV_Y,5,
    PANEL_NOTIFY_PROC,LerGrupos,
    XV_HELP_DATA,"asiz:brsensi",
    NULL);
  bwsensi=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Write",
    XV_X,250,
    XV_Y,32,
    PANEL_NOTIFY_PROC,EscreverGrupos,
    XV_HELP_DATA,"asiz:bwsensi",
    NULL);
  csensi=xv_create(jsensi,CANVAS,
    WIN_CMS,cms,
    CANVAS_X_PAINT_WINDOW,TRUE,
    CANVAS_REPAINT_PROC,PlotarSensi,
    XV_Y,90,
    XV_HELP_DATA,"asiz:csensi",
    NULL);

  xv_set(canvas_paint_window(csensi),
    WIN_EVENT_PROC,MudarElementos,
    WIN_CONSUME_EVENTS,
      WIN_ASCII_EVENTS, LOC_DRAG, LOC_MOVE, WIN_MOUSE_BUTTONS,
      WIN_TOP_KEYS, WIN_META_EVENTS,
      NULL,
    WIN_IGNORE_EVENTS, WIN_UP_EVENTS, WIN_UP_ASCII_EVENTS,
      NULL,
    NULL);

  jrelatorio=xv_create(jfrequencia,FRAME_CMD,
    XV_LABEL,"Report File",
    XV_X,10,
    XV_Y,100,
    NULL);
  panel=(Panel)xv_get(jrelatorio,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  trelatorio=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Filename",
    PANEL_VALUE_DISPLAY_LENGTH,21,
    NULL);
  brelatorio=xv_create(panel,PANEL_BUTTON,
    PANEL_LABEL_STRING,"Open",
    PANEL_NOTIFY_PROC,AbrirRelatorio,
    NULL);
  window_fit(panel);
  window_fit(jrelatorio);

/*
  jdiretorio=xv_create(jfrequencia,FRAME,
    XV_LABEL,"Directory",
    XV_WIDTH,300,
    XV_X,10,
    XV_Y,200,
    XV_HEIGHT,300,
    NULL);
  panel=xv_create(jdiretorio,PANEL,
    XV_X,0,
    XV_Y,0,
    XV_WIDTH,WIN_EXTEND_TO_EDGE,
    XV_HEIGHT,30,
    NULL);
  tmask=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Mask",
    PANEL_VALUE_DISPLAY_LENGTH,24,
    PANEL_VALUE,"*.net",
    PANEL_NOTIFY_PROC,LerDiretorio,
    NULL);
  cdiretorio=xv_create(jdiretorio,CANVAS,
    XV_Y,30,
    WIN_CMS,cms,
    CANVAS_X_PAINT_WINDOW,TRUE,
    CANVAS_REPAINT_PROC,LerDiretorio,
    NULL);

  xv_set(canvas_paint_window(cdiretorio),
    WIN_EVENT_PROC,EscolherArquivo,
    WIN_CONSUME_EVENTS,
      WIN_ASCII_EVENTS, LOC_DRAG, LOC_MOVE, WIN_MOUSE_BUTTONS,
      WIN_TOP_KEYS, WIN_META_EVENTS,
      NULL,
    WIN_IGNORE_EVENTS, WIN_UP_EVENTS, WIN_UP_ASCII_EVENTS,
      NULL,
    NULL);
*/

  jmos=xv_create(jfrequencia,FRAME_CMD,
    XV_LABEL,"MOSFET Parameters",
    XV_X,10,
    XV_Y,100,
    NULL);
  panel=(Panel)xv_get(jmos,FRAME_CMD_PANEL);
  xv_set(panel,PANEL_LAYOUT,PANEL_VERTICAL,NULL);
  scap=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Cgs,Cgd",
    PANEL_CHOICE_STRINGS,"1,0","proportional to Gm",NULL,
    PANEL_VALUE,0,
    PANEL_NOTIFY_PROC,InvalidarNetlist,
    XV_HELP_DATA,"asiz:scap",
    NULL);
  tcgs=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Cgs for Gm=1",
    PANEL_VALUE_DISPLAY_LENGTH,6,
    PANEL_VALUE,"1.0",
    PANEL_NOTIFY_PROC,InvalidarNetlist,
    XV_HELP_DATA,"asiz:tcgs",
    NULL);
  tcgd=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Cgd for Gm=1",
    PANEL_VALUE_DISPLAY_LENGTH,6,
    PANEL_VALUE,"1e-2",
    PANEL_NOTIFY_PROC,InvalidarNetlist,
    XV_HELP_DATA,"asiz:tcgd",
    NULL);
  sgds=xv_create(panel,PANEL_CHOICE,
    PANEL_LABEL_STRING,"Gds",
    PANEL_CHOICE_STRINGS,"as read","proportional to Gm",NULL,
    PANEL_VALUE,0,
    PANEL_NOTIFY_PROC,InvalidarNetlist,
    XV_HELP_DATA,"asiz:sgds",
    NULL);
  tgds=xv_create(panel,PANEL_TEXT,
    PANEL_LABEL_STRING,"Gds for Gm=1",
    PANEL_VALUE_DISPLAY_LENGTH,6,
    PANEL_VALUE,"1e-2",
    PANEL_NOTIFY_PROC,InvalidarNetlist,
    XV_HELP_DATA,"asiz:tgds",
    NULL);
  window_fit(panel);
  window_fit(jmos);

  open_window(jfrequencia);
  /*open_window(jdiretorio);*/
  xv_main_loop(jnetlist);
  if (relatorio) fclose(arquivo);
  printf("ASIZ terminated\n");
  exit(0);
}

/* End. */
