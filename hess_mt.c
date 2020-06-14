/*
///////////////////////////////////////////////////////////////////////////////
//        Copyright (c) 2012-2020 Oscar Riveros. all rights reserved.        //
//                        oscar.riveros@peqnp.science                        //
//                                                                           //
//   without any restriction, Oscar Riveros reserved rights, patents and     //
//  commercialization of this knowledge or derived directly from this work.  //
///////////////////////////////////////////////////////////////////////////////

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/

#include <memory.h>
#include <stdio.h>
#include <stdlib.h>
#include "tinycthread.h"
// #include <threads.h>

mtx_t mutex;

int n;
int m;
int n_threads;
int *sizes;
int **cls;
int solved;
int cursor;

struct node {
    int id;
    int *model;
    int *temporal;
    int *optimal;
};

int oracle (struct node *node)
{
  int i, j, c = 0;
  for (i = 0; i < n; i++) {
    node->temporal[i] = node->model[i] ? +(i + 1) : -(i + 1);
  }
  for (i = 0; i < m; i++) {
    for (j = 0; j < sizes[i]; j++) {
      if (cls[i][j] == node->temporal[labs (cls[i][j]) - 1]) {
        c++;
        if (c > cursor) {
          return c;
        }
        break;
      }
    }
  }
  return c;
}

void step(int i, int j, struct node *node) {
  int aux;
  if (node->model[i] == node->model[j]) {
    node->model[i] = !node->model[j];
  } else {
    aux = node->model[i];
    node->model[i] = !node->model[j];
    node->model[j] = aux;
  }
}

int hess (struct node *node)
{
  int i, j, k, c, loc, glb;
  cursor = 0;
  c = 0;
  do {
    glb = 0;
    o:
    for (i = 0; i < n; i++) {
      oo:
      for (j = 0; j < n; j++) {
        ooo:
        if (solved) {
          return -1;
        }
        step (i, j, node);
        loc = oracle (node);
        if (loc > glb) {
          glb = loc;
          if (glb > cursor) {
            cursor = glb;
            if (solved == 0) {
#ifdef LOG
              printf ("\rc REMAINING : %3.2lf%% [%d] ", 100.0 - 100.0 * cursor / m, node->id);
              fflush (stdout);
#endif

            }
            memcpy(node->optimal, node->model, sizeof (int) * n);
            if (m == cursor) {
              solved = 1;
              return 1;
            }
            goto o;
          }
          goto oo;
        } else if (loc < glb) {
          goto ooo;
        }
      }
    }
    for (i = 0; i < n; i++) {
      node->model[i] = !node->model[i];
    }
  } while (c++ <= m * n);
  solved = 1;
  return 0;
}

int apply (int id)
{
  int i, j, result;
  struct node node;

  node.id = id;
  node.temporal = (int *) calloc ((size_t) n, sizeof (int));
  node.model = (int *) calloc ((size_t) n, sizeof (int));
  node.optimal = (int *) calloc ((size_t) n, sizeof (int));

  for (i = 0; i < n; i++) {
    node.model[i] = ((i + 1) * (id + 1)) % 2;
  }

  result = hess (&node);

  mtx_lock (&mutex);
  if (result == 1) {
    printf ("\ns SATISFIABLE");
    for (i = 0; i < n; i++) {
      if (i % 10 == 0) {
        printf ("\nv ");
      }
      printf ("%i ", node.optimal[i] ? +(i + 1) : -(i + 1));
    }
    printf ("0\n");
  }
  if (result == 0) {
    printf ("\ns UNSATISFIABLE\n");
  }

  free (node.temporal);
  free (node.model);
  free (node.optimal);

  mtx_unlock (&mutex);

  return 1;
}

int main (int argc, char **argv)
{
  int i, j;
  char buffer[32];

  if (argc != 3) {
    printf ("c /////////////////////////////////////////////////////////////////////////////\n");
    printf ("c //       Copyright (c) 2012-2020 Oscar Riveros. all rights reserved.       //\n");
    printf ("c //                       oscar.riveros@peqnp.science                       //\n");
    printf ("c //                                                                         //\n");
    printf ("c //  without any restriction, Oscar Riveros reserved rights, patents and    //\n");
    printf ("c // commercialization of this knowledge or derived directly from this work. //\n");
    printf ("c /////////////////////////////////////////////////////////////////////////////\n");
    printf ("c                                                                              \n");
    printf ("c usage: %s <instance> <n-threads>\n", argv[0]);
    return EXIT_FAILURE;
  }

  printf ("c               \n");
  printf ("c ╦ ╦╔═╗╔═╗╔═╗  \n");
  printf ("c ╠═╣║╣ ╚═╗╚═╗  \n");
  printf ("c ╩ ╩╚═╝╚═╝╚═╝  \n");
  printf ("c www.peqnp.com \n");
  printf ("c                  \n");
  printf ("c INSTANCE  : %s\n", argv[1]);

  FILE *file = fopen (argv[1], "r");
  if (strcmp (buffer, "c") == 0) {
    while (strcmp (buffer, "\n") != 0) {
      fscanf (file, "%s", buffer);
    }
  }
  while (strcmp (buffer, "p") != 0) {
    fscanf (file, "%s", buffer);
  }
  fscanf (file, " cnf %i %i", &n, &m);
  sizes = (int *) calloc ((size_t) m, sizeof (int));
  cls = (int **) calloc ((size_t) m, sizeof (int *));

  printf ("c VARIABLES : %d\n", n);
  printf ("c CLAUSES   : %d\n", m);
  printf ("c RATIO     : %lf\n", (double) m / n);

  for (i = 0; i < m; i++) {
#ifdef LOG
    printf ("\rc LOADING   : %3.2lf%%", 100.0 * (i + 1) / m);
    fflush (stdout);
#endif
    j = 0;
    cls[i] = (int *) calloc ((size_t) n, sizeof (int));
    do {
      fscanf (file, "%s", buffer);
      if (strcmp (buffer, "c") == 0) {
        continue;
      }
      cls[i][j++] = atoi (buffer);
    } while (strcmp (buffer, "0") != 0);
    j--;
    cls[i] = (int *) realloc (cls[i], j * sizeof (int));
    sizes[i] = j;
  }
  fclose (file);

  solved = 0;

  mtx_init (&mutex, mtx_plain);

  n_threads = atoi (argv[2]);

  thrd_t *thread_id = (thrd_t *) calloc ((size_t) n_threads, sizeof (thread_id));
  for (i = 0; i < n_threads; ++i) {
    if (thrd_create (thread_id + i, apply, i) != thrd_success) {
      printf ("%d-th thread create error\n", i);
      return 0;
    }
  }

  for (i = 0; i < n_threads; ++i) {
    thrd_join (thread_id[i], NULL);
  }

  free (sizes);
  free (cls);

  return EXIT_SUCCESS;
}