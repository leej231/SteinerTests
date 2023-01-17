import gurobipy as gp
from gurobipy import GRB
import matplotlib.pyplot as plt
import ast
import math
import random
import time
import numpy as np
from itertools import combinations
from shapely.geometry import Point, MultiPoint
from shapely.geometry.polygon import LinearRing


def gridloc(point):
    a = math.floor(point[0] * ff)
    b = math.floor(point[1] * gg)
    if a < 0:
        a = 0
    if b < 0:
        b = 0
    if a >= ff:
        a = ff - 1
    if b >= gg:
        b = gg - 1
    return a, b


def gridrange(pointlist):
    xvals = []
    yvals = []
    for point in pointlist:
        x, y = gridloc(point)
        xvals.append(x)
        yvals.append(y)
    return min(xvals), max(xvals), min(yvals), max(yvals)


def find(lst, a):
    return [i for i, x in enumerate(lst) if x == a]


class Graph:
    def __init__(self, vertex):
        self.V = vertex
        self.graph = []

    def add_edge(self, u, v, w):
        self.graph.append([u, v, w])

    def search(self, parent, i):
        if parent[i] == i:
            return i
        return self.search(parent, parent[i])

    def apply_union(self, parent, rank, x, y):
        xroot = self.search(parent, x)
        yroot = self.search(parent, y)
        if rank[xroot] < rank[yroot]:
            parent[xroot] = yroot
        elif rank[xroot] > rank[yroot]:
            parent[yroot] = xroot
        else:
            parent[yroot] = xroot
            rank[xroot] += 1

    def kruskal(self):
        result = []
        i, e = 0, 0
        self.graph = sorted(self.graph, key=lambda item: item[2])
        parent = []
        rank = []
        for node in range(self.V):
            parent.append(node)
            rank.append(0)
        while e < self.V - 1:
            u, v, w = self.graph[i]
            i = i + 1
            x = self.search(parent, u)
            y = self.search(parent, v)
            if x != y:
                e = e + 1
                result.append([u, v, w])
                self.apply_union(parent, rank, x, y)
        return result


def find_angle(p1, p2):  # finds angle in degrees of p2 from p1, 0 degrees is parallel to the x-axis, to the right
    rise = p2[1] - p1[1]
    run = p2[0] - p1[0]
    if run == 0:
        if rise == 0:
            return
        if rise > 0:
            return 90
        if rise < 0:
            return 270
    else:
        return math.degrees(math.atan2(rise, run))


def closest_point_on_line(p1, p2, p3):  # p1,p2 are on line, p3 is your third point
    x1, y1 = p1
    x2, y2 = p2
    x3, y3 = p3
    dx, dy = x2 - x1, y2 - y1
    det = dx * dx + dy * dy
    a = (dy * (y3 - y1) + dx * (x3 - x1)) / det
    return [x1 + a * dx, y1 + a * dy]


def circ_line_cartesian(p1, p2, p3,
                        centre):  # p1 source point, p2 line point, p3 point in question, this is a lemma for circ_line_relocate
    closest_horizontal = closest_point_on_line(p1, p2, p3)
    x_val = point_distance(p1, closest_horizontal)
    if same_side(p3, centre, p1, closest_horizontal):
        y_val = point_distance(p3, closest_horizontal)
    else:
        y_val = - point_distance(p3, closest_horizontal)
    return [x_val, y_val]


def rotated_point(p1, p2, angle):  # rotates p2 around p1 by given angle
    qx = p1[0] + math.cos(math.radians(angle)) * (p2[0] - p1[0]) - math.sin(math.radians(angle)) * (p2[1] - p1[1])
    qy = p1[1] + math.sin(math.radians(angle)) * (p2[0] - p1[0]) + math.cos(math.radians(angle)) * (p2[1] - p1[1])
    return [qx, qy]


def point_distance(p1, p2):
    return math.sqrt((p1[0] - p2[0]) ** 2 + (p1[1] - p2[1]) ** 2)


def point_to_line_distance(p1, p2, p3):  # distance from p3 to line through p1,p2
    if p1[1] == p2[1]:
        if p1[0] <= p3[0] <= p2[0] or p2[0] <= p3[0] <= p1[0]:
            return p3[1] - p1[1]
        else:
            return min(point_distance(p1, p3), point_distance(p2, p3))
    else:
        gradient = -(p2[0] - p1[0]) / (p2[1] - p1[1])
        new_point = [p3[0] + 1, p3[1] + gradient]
        intersect = find_intersection(p1, p2, p3, new_point)
        if p1[0] <= intersect[0] <= p2[0] or p2[0] <= intersect[0] <= p1[0]:
            return point_distance(p3, intersect)
        else:
            return min(point_distance(p1, p3), point_distance(p2, p3))


def line_to_line_distance(p1, p2, p3, p4):
    return min([point_to_line_distance(p1, p2, p3), point_to_line_distance(p1, p2, p4), point_to_line_distance(p3, p4, p1),
                point_to_line_distance(p3, p4, p2)])


def equipoint2(p1, p2):
    newpoint = rotated_point(p1, p2, 60)
    return [newpoint[0], newpoint[1], [p1, p2], p1[:2], p2[:2], p1[5] + p2[5] + 1,
            p1[6] + p2[6]]  # note final addition is a list addition


def equipoint3(p1, p2, p3):
    if p1[3] == p1[4] == [-1, -1]:
        return [p1[0], p1[1], [p1, p2, p3], p2[:2], p3[:2], p1[5] + p2[5] + p3[5] + 1,
                p1[6] + p2[6] + p3[6]]  # note final addition is a list addition
    else:
        new_params = IntervalProjectionTest(p1, p2, p3)
        return [p1[0], p1[1], [p1, p2, p3], new_params[0], new_params[1], p1[5] + p2[5] + p3[5] + 1,
                p1[6] + p2[6] + p3[6]]  # note final addition is a list addition


def get_angle(a, b, c):  # finds angle between these three points at b, taken clockwise
    ang = math.degrees(math.atan2(c[1] - b[1], c[0] - b[0]) - math.atan2(a[1] - b[1], a[0] - b[0]))
    return ang


def find_intersection(A, B, C, D):  # intersection of line through A,B with line through C,D
    px = ((A[0] * B[1] - A[1] * B[0]) * (C[0] - D[0]) - (A[0] - B[0]) * (C[0] * D[1] - C[1] * D[0])) / (
            (A[0] - B[0]) * (C[1] - D[1]) - (A[1] - B[1]) * (C[0] - D[0]))
    py = ((A[0] * B[1] - A[1] * B[0]) * (C[1] - D[1]) - (A[1] - B[1]) * (C[0] * D[1] - C[1] * D[0])) / (
            (A[0] - B[0]) * (C[1] - D[1]) - (A[1] - B[1]) * (C[0] - D[0]))
    return [px, py]


def steiner(A, B, C):
    a = get_angle(B, A, C)
    b = get_angle(C, B, A)
    c = get_angle(A, C, B)
    if 120 <= a <= 240:
        return A
    elif 120 <= b <= 240:
        return B
    elif 120 <= c <= 240:
        return C
    else:
        if LinearRing([A, B, C]).is_ccw:
            return find_intersection(C, rotated_point(B, A, 60), B, rotated_point(A, C, 60))
        else:
            return find_intersection(B, rotated_point(C, A, 60), C, rotated_point(A, B, 60))


def dist_constraint(p1, p2,
                   p3):  # Marcus conjecture where n=1/(2*sqrt(3) . Formula straight from wiki page on point to a line with small modifications. p3 is the point we are checking the distance from the interval p1-p2
    return abs((p2[0] - p1[0]) * (p1[1] - p3[1]) - (p1[0] - p3[0]) * (p2[1] - p1[1])) <= (1 / (2 * math.sqrt(3))) * (
            (p2[0] - p1[0]) ** 2 + (p2[1] - p1[1]) ** 2)


def reverse_dist(p1, p2, p3):  # p3 is the point we are checking distance from interval p1-p2
    m = 1 / (2 * math.sqrt(3))
    return (((1 - 2 * m ** 2) / (2 * m)) * ((p2[0] - p1[0]) ** 2 + (p2[1] - p1[1]) ** 2) < abs(
        (p2[0] - p1[0]) * (p1[1] - p3[1]) - (p1[0] - p3[0]) * (p2[1] - p1[1])))


def terms_in_lune(x, y, terms,
                allowed):  # returns True if there is no terminal in the lune of x and y that is not in the allowed list
    lunes_empty = True
    for j in terms:  # check lune constraint using proposed edges
        if lune_constraint(x, y, j) and j[:2] not in [x[:2], y[:2]] + [point[:2] for point in allowed]:
            lunes_empty = False
            break
    return lunes_empty


def lune_constraint(p1, p2, p3):  # returns true if p3 is inside the lune of p1 and p2
    xx = point_distance(p1, p2)
    return (point_distance(p3, p2) <= xx) and (point_distance(p3, p1) <= xx)


def bottle_constraint(list1, stein, terms, bottle):
    terms_short = [x[:2] for x in terms]
    for point in list1:
        x = point_distance(point, stein)
        for second_point in list1[(list1.index(point) + 1):]:
            if x > bottle[terms_short.index(point)][terms_short.index(second_point)]:
                return False
    return True


def quad_constraint(p1, p2, p3):  # returns true if p3 is inside the quad of p1 and p2
    quad = [p1[:2], rotated_point(p1, p2, 60), p2[:2], rotated_point(p2, p1, 60)]
    return ray_tracing_method(p3[0], p3[1], quad)


def same_side(u, v, x, y):  # returns true if both u and v are on the same side of x and y
    if y[0] == x[0]:
        return (u[0] <= x[0] and v[0] <= x[0]) or (u[0] >= x[0] and v[0] >= x[0])
    else:
        m = (y[1] - x[1]) / (y[0] - x[0])
        return ((u[1] - m * u[0] >= x[1] - m * x[0]) and (v[1] - m * v[0] >= x[1] - m * x[0])) or (
                    (u[1] - m * u[0] <= x[1] - m * x[0]) and (v[1] - m * v[0] <= x[1] - m * x[0]))


def same_side3(p1, p2, p3):  # True if p2 and p3 are on same side of p1
    if p1[0] == p2[0] == p3[0]:
        return not ((p2[1] < p1[1] < p3[1]) or (p3[1] < p1[1] < p2[1]))
    else:
        return not ((p2[0] < p1[0] < p3[0]) or (p3[0] < p1[0] < p2[0]))


def alpha_ext(u, v, x,
              y):  # iterated version of alpha constraint, simple application. Returns false if both u and v fail the alpha constraint. Requires both u and v to be on the same side of the xy line
    alpha_con = point_distance(x, y) * (1 / (2 * math.sqrt(3)))
    if same_side(u, v, x, y):
        if y[0] == x[0]:
            if u[0] >= x[0]:
                return not ((u[0] <= x[0] + alpha_con) and (v[0] <= x[0] + alpha_con))
            else:
                return not ((u[0] <= x[0] - alpha_con) and (v[0] <= x[0] - alpha_con))
        else:
            m = (y[1] - x[1]) / (y[0] - x[0])
            if u[1] - m * u[0] >= x[1] - m * x[0]:
                return not ((u[1] - m * u[0] <= x[1] - m * x[0] + alpha_con) and (
                            v[1] - m * v[0] <= x[1] - m * x[0] + alpha_con))
            else:
                return not ((u[1] - m * u[0] <= x[1] - m * x[0] - alpha_con) and (
                            v[1] - m * v[0] <= x[1] - m * x[0] - alpha_con))
    else:
        return True


def vertical_constraint(p1, p2, p3, p4):  # check if p3,p4 is in Jae's vertical constraint made by p1,p2.
    if p1[1] == p2[1]:
        return (min(p1[0], p2[0]) <= p3[0] <= max(p1[0], p2[0])) and (min(p1[0], p2[0]) <= p4[0] <= max(p1[0], p2[0]))
    else:
        m = -(p1[0] - p2[0]) / (p1[1] - p2[1])
        return (min(p1[1] - m * p1[0], p2[1] - m * p2[0]) <= p3[1] - m * p3[0] <= max(p1[1] - m * p1[0],
                                                                                      p2[1] - m * p2[0])) and (
                       min(p1[1] - m * p1[0], p2[1] - m * p2[0]) <= p4[1] - m * p4[0] <= max(p1[1] - m * p1[0],
                                                                                             p2[1] - m * p2[0]))


def find_terminals(list1):
    terminallist = []
    for i in list1:
        if not any(isinstance(j, list) for j in i):
            terminallist.append(i)
        else:
            terminallist.extend(find_terminals(i))
    return terminallist


def ProjectionToArc(z, proj):
    if len(z[2]) == 2:
        return [point for point in ArcLineInter(z, proj, z) if point != z][0]
    else:
        return find_intersection(z, proj, z[2][1], z[2][2])


def is_point_in_cone(eqpoint1, eqpoint2):  # checks if eqpoint2 is in cone of eqpoint1
    if eqpoint1[3] == eqpoint1[4] == [-1, -1]:  # dummy locations for order-0 pseudoterminals
        return True
    else:
        angle_to_point = find_angle(eqpoint1[:2], eqpoint2[:2])
        angle_to_base1 = find_angle(eqpoint1[:2], eqpoint1[3])
        angle_to_base2 = find_angle(eqpoint1[:2], eqpoint1[4])
        if angle_to_base1 <= -120 and angle_to_base2 >= 120:
            angle_to_base1 += 360
            if angle_to_point <= 120:
                angle_to_point += 360
            return angle_to_base2 < angle_to_point < angle_to_base1
        elif angle_to_base2 <= -120 and angle_to_base1 >= 120:
            angle_to_base2 += 360
            if angle_to_point <= 120:
                angle_to_point += 360
            return angle_to_base1 < angle_to_point < angle_to_base2
        else:
            return angle_to_base1 < angle_to_point < angle_to_base2 or angle_to_base2 < angle_to_point < angle_to_base1


def IntervalProjectionTest(point, x,
                           y):  # returns false if interval not in cone, otherwise returns new arc/line endpoints
    if point[3] == point[4] == [-1, -1]:  # dummy locations for order-0 pseudoterminals
        return point[3], point[4]
    angle_to_point1 = find_angle(point, point[3])
    angle_to_point2 = find_angle(point, point[4])
    angle_to_base1 = find_angle(point, x)
    angle_to_base2 = find_angle(point, y)
    if angle_to_base1 <= -120 and angle_to_base2 >= 120:
        angle_to_base1 += 360
        if angle_to_point1 <= 120:
            angle_to_point1 += 360
        if angle_to_point2 <= 120:
            angle_to_point2 += 360
    elif angle_to_base2 <= -120 and angle_to_base1 >= 120:
        angle_to_base2 += 360
        if angle_to_point1 <= 120:
            angle_to_point1 += 360
        if angle_to_point2 <= 120:
            angle_to_point2 += 360
    point1inside = (angle_to_base1 <= angle_to_point1 <= angle_to_base2) or (angle_to_base2 <= angle_to_point1 <= angle_to_base1)
    point2inside = (angle_to_base1 <= angle_to_point2 <= angle_to_base2) or (angle_to_base2 <= angle_to_point2 <= angle_to_base1)
    if point1inside and point2inside:
        return point[3], point[4]
    elif not point1inside and not point2inside:
        return False, False
    elif not point1inside and point2inside:
        if (angle_to_point1 <= angle_to_base1 <= angle_to_point2) or (angle_to_point2 <= angle_to_base1 <= angle_to_point1):
            return x, point[4]
        else:
            return y, point[4]
    else:
        if (angle_to_point1 <= angle_to_base1 <= angle_to_point2) or (angle_to_point2 <= angle_to_base1 <= angle_to_point1):
            return point[3], x
        else:
            return point[3], y


def DoConesOverlap(p1, p2):
    if p1[3] == p1[4] == [-1, -1] or p2[3] == p2[4] == [-1, -1]:
        return True
    else:
        a = find_intersection(p1, p1[3], p2, p2[3])
        b = find_intersection(p1, p1[3], p2, p2[4])
        c = find_intersection(p1, p1[4], p2, p2[3])
        d = find_intersection(p1, p1[4], p2, p2[4])
        first_point = (same_side3(p1, p1[3], a) and same_side3(p2, p2[3], a)) or (
                    same_side3(p1, p1[3], b) and same_side3(p2, p2[4], b))
        second_point = (same_side3(p1, p1[4], c) and same_side3(p2, p2[3], c)) or (
                    same_side3(p1, p1[4], d) and same_side3(p2, p2[4], d))
        return first_point or second_point


def reverse_melzak(point1, point2):
    edge_list = []
    if not melzak_check(point1, point2):
        edge_list.append(False)
    if len(point1[2]) == 0:
        first = point1[:2]
    else:
        if len(point1[2]) == 2:
            first = steiner(point2[:2], point1[2][0][:2], point1[2][1][:2]) + [[], [-1, -1], [-1, -1], 0, [-1]]
            edge_list.extend(reverse_melzak(first, point1[2][0]))
            edge_list.extend(reverse_melzak(first, point1[2][1]))
        else:
            first = find_intersection(point2[:2], point1[2][0][:2], point1[2][1][:2], point1[2][2][:2]) + [[], [-1, -1],
                                                                                                          [-1, -1], 0,
                                                                                                          [-1]]
            edge_list.extend(reverse_melzak(first, point1[2][0]))
            edge_list.extend(reverse_melzak(first, point1[2][1]))
            edge_list.extend(reverse_melzak(first, point1[2][2]))
    if len(point2[2]) == 0:
        second = point2[:2]
    else:
        if len(point2[2]) == 2:
            second = steiner(point1[:2], point2[2][0][:2], point2[2][1][:2]) + [[], [-1, -1], [-1, -1], 0, [-1]]
            edge_list.extend(reverse_melzak(second, point2[2][0]))
            edge_list.extend(reverse_melzak(second, point2[2][1]))
        else:
            second = find_intersection(point1[:2], point2[2][0][:2], point2[2][1][:2], point2[2][2][:2]) + [[], [-1, -1],
                                                                                                           [-1, -1],
                                                                                                           0, [-1]]
            edge_list.extend(reverse_melzak(second, point2[2][0]))
            edge_list.extend(reverse_melzak(second, point2[2][1]))
            edge_list.extend(reverse_melzak(second, point2[2][2]))
    edge_list.append([first[:2], second[:2]])
    return edge_list


def NonPseudoPair(point1, point2):
    if len(point1[2]) == 0:
        first = point1
    else:
        if len(point1[2]) == 2:
            first = steiner(point2[:2], point1[2][0][:2], point1[2][1][:2]) + [[], [-1, -1], [-1, -1], 0, [-1]]
        else:
            first = find_intersection(point2[:2], point1[2][0][:2], point1[2][1][:2], point1[2][2][:2]) + [[], [-1, -1],
                                                                                                          [-1, -1], 0,
                                                                                                          [-1]]
    if len(point2[2]) == 0:
        second = point2
    else:
        if len(point2[2]) == 2:
            second = steiner(point1[:2], point2[2][0][:2], point2[2][1][:2]) + [[], [-1, -1], [-1, -1], 0, [-1]]
        else:
            second = find_intersection(point1[:2], point2[2][0][:2], point2[2][1][:2], point2[2][2][:2]) + [[], [-1, -1],
                                                                                                           [-1, -1],
                                                                                                           0, [-1]]
    return first, second


def find_circle(p1, p2, p3):  # finds circle given three points on it. Output is centre, radius
    if p2[0] == p1[0]:
        m1 = 0
    else:
        m1 = (p1[0] - p2[0]) / (p2[1] - p1[1])  # negative reciprocal of gradient of line through p1 and p2
    if p3[0] == p1[0]:
        m2 = 0
    else:
        m2 = (p1[0] - p3[0]) / (p3[1] - p1[1])  # negative reciprocal of gradient of line through p1 and p2
    midpoint1 = [(p1[0] + p2[0]) / 2, (p1[1] + p2[1]) / 2]
    midpoint2 = [(p1[0] + p3[0]) / 2, (p1[1] + p3[1]) / 2]
    centre = find_intersection(midpoint1, [midpoint1[0] + 1, midpoint1[1] + m1], midpoint2,
                              [midpoint2[0] + 1, midpoint2[1] + m2])
    radius = point_distance(centre, p1)
    return centre, radius


def circle_line_segment_intersection(circle_center, circle_radius, pt1, pt2, full_line=True, tangent_tol=1e-9):
    """ Find the points at which a circle intersects a line-segment.  This can happen at 0, 1, or 2 points.

    :param circle_center: The (x, y) location of the circle center
    :param circle_radius: The radius of the circle
    :param pt1: The (x, y) location of the first point of the segment
    :param pt2: The (x, y) location of the second point of the segment
    :param full_line: True to find intersections along full line - not just in the segment.  False will just return intersections within the segment.
    :param tangent_tol: Numerical tolerance at which we decide the intersections are close enough to consider it a tangent
    :return Sequence[Tuple[float, float]]: A list of length 0, 1, or 2, where each element is a point at which the circle intercepts a line segment.

    Note: We follow: http://mathworld.wolfram.com/Circle-LineIntersection.html
    """

    (p1x, p1y), (p2x, p2y), (cx, cy) = pt1, pt2, circle_center
    (x1, y1), (x2, y2) = (p1x - cx, p1y - cy), (p2x - cx, p2y - cy)
    dx, dy = (x2 - x1), (y2 - y1)
    dr = (dx ** 2 + dy ** 2) ** .5
    big_d = x1 * y2 - x2 * y1
    discriminant = circle_radius ** 2 * dr ** 2 - big_d ** 2

    if discriminant < 0:  # No intersection between circle and line
        return []
    else:  # There may be 0, 1, or 2 intersections with the segment
        intersections = [
            (cx + (big_d * dy + sign * (-1 if dy < 0 else 1) * dx * discriminant ** .5) / dr ** 2,
             cy + (-big_d * dx + sign * abs(dy) * discriminant ** .5) / dr ** 2)
            for sign in ((1, -1) if dy < 0 else (-1, 1))]  # This makes sure the order along the segment is correct
        if not full_line:  # If only considering the segment, filter out intersections that do not fall within the segment
            fraction_along_segment = [(xi - p1x) / dx if abs(dx) > abs(dy) else (yi - p1y) / dy for xi, yi in
                                      intersections]
            intersections = [pt for pt, frac in zip(intersections, fraction_along_segment) if 0 <= frac <= 1]
        if len(intersections) == 2 and abs(
                discriminant) <= tangent_tol:  # If line is tangent to circle, return just one point (as both intersections have same location)
            return [intersections[0]]
        else:
            return intersections


def ArcLineInter(point, linepoint1, linepoint2):
    centre, radius = find_circle(point[:2], point[3][:2], point[4][:2])
    intersections = circle_line_segment_intersection(centre, radius, linepoint1[:2], linepoint2[:2])
    if len(intersections) == 0:
        return None
    else:
        return intersections
        # Note this might return two points - if you are expecting just one to be on arc, try following code:
        # base_point = [centre[0],centre[1],[],point[3],point[4],]
        # if is_point_in_cone(base_point,intersections[0]):
        #     return intersections[0]
        # else:
        #     return intersections[1]


def rhombus_ext(point, x, y):  # returns False if arc does not have any points in the rhombus
    if point[3] == point[4] == [-1, -1]:
        return quad_constraint(x, y, point)
    else:
        if not quad_constraint(x, y, point[3]) and not quad_constraint(x, y, point[4]):
            eqpoint1 = equipoint2(x, y)
            eqpoint2 = equipoint2(y, x)
            if ([ArcLineInter(point, x, eqpoint1) is None, ArcLineInter(point, x, eqpoint2) is None, ArcLineInter(point, y, eqpoint1) is None, ArcLineInter(
                    point, x, eqpoint2) is None, ArcLineInter(point, x, eqpoint2) is None]).all():
                return False
        else:
            return True


def tangentpoint(x, y, centre_x, centre_y,
                 radius):  # finds the two points on a circle for which the tangent passes through x,y
    b = math.sqrt((x - centre_x) ** 2 + (y - centre_y) ** 2)
    th = math.acos(radius / b)  # angle theta
    d = math.atan2(y - centre_y, x - centre_x)  # direction angle of point P from C
    d1 = d + th  # direction angle of point T1 from C
    d2 = d - th  # direction angle of point T2 from C

    T1x = centre_x + radius * math.cos(d1)
    T1y = centre_y + radius * math.sin(d1)
    T2x = centre_x + radius * math.cos(d2)
    T2y = centre_y + radius * math.sin(d2)
    return [T1x, T1y], [T2x, T2y]


def ray_tracing_method(x, y, poly):  # returns true if x,y is in poly

    n = len(poly)
    inside = False

    p1x, p1y = poly[0]
    for i in range(n + 1):
        p2x, p2y = poly[i % n]
        if y > min(p1y, p2y):
            if y <= max(p1y, p2y):
                if x <= max(p1x, p2x):
                    if p1y != p2y:
                        xints = (y - p1y) * (p2x - p1x) / (p2y - p1y) + p1x
                    if p1x == p2x or x <= xints:
                        inside = not inside
        p1x, p1y = p2x, p2y

    return inside


def triangle_ext(point, x, y,
                 grid_terms):  # returns true if triangle is empty, must be done after IntervalProjectionTest
    vertices = [point[:2], x[:2], y[:2]]
    # polygon = Polygon(vertices)
    if len(point[2]) > 0:
        # first find the points on the arc that give a tangent through x,y, or take u,v if they lie outside the arc
        circle_centre, circle_radius = find_circle(point[:2], point[3], point[4])
        rhs = find_intersection(point[:2], point[3], x, y)
        lhs = find_intersection(point[:2], point[4], x, y)
        rhs_tangent1, rhs_tangent2 = tangentpoint(rhs[0], rhs[1], circle_centre[0], circle_centre[1], circle_radius)
        lhs_tangent1, lhs_tangent2 = tangentpoint(lhs[0], lhs[1], circle_centre[0], circle_centre[1], circle_radius)
        lhs_poss = []
        rhs_poss = []
        if is_point_in_cone(point, lhs_tangent1):
            lhs_poss.append(lhs_tangent1)
        if is_point_in_cone(point, lhs_tangent2):
            lhs_poss.append(lhs_tangent2)
        if is_point_in_cone(point, rhs_tangent1):
            rhs_poss.append(rhs_tangent1)
        if is_point_in_cone(point, rhs_tangent2):
            rhs_poss.append(rhs_tangent2)
        tang_point1 = point[3]
        tang_point2 = point[4]

        if len(rhs_poss) > 0:
            rhs_poss = sorted(rhs_poss, key=lambda val: point_distance(val, point[4]))
            tang_point2 = rhs_poss[0]
        if len(lhs_poss) > 0:
            lhs_poss = sorted(lhs_poss, key=lambda val: point_distance(val, point[3]))
            tang_point1 = lhs_poss[0]

        top = find_intersection(tang_point1, x, tang_point2, y)
        if not ray_tracing_method(top[0], top[1], vertices):
            top = find_intersection(tang_point1, y, tang_point2, x)
        vertices = [top, x[:2], y[:2]]
        # polygon = Polygon([top,x[:2],y[:2]])
    polygon_empty = True
    xmin, xmax, ymin, ymax = gridrange(vertices)
    for xx in range(xmin, xmax + 1):
        for yy in range(ymin, ymax + 1):
            for point in grid_terms[xx][yy]:
                if ray_tracing_method(point[0], point[1], vertices) and point[:2] not in vertices:
                    polygon_empty = False
                    break
            if not polygon_empty:
                break
        if not polygon_empty:
            break
    return polygon_empty


def bottle_ext(x, y, z, bottleneck):
    bot_dist = []
    for a in z[6]:
        for b in y[6] + x[6]:
            bot_dist.append(bottleneck[a][b])
    if len(z[2]) == 0:
        distance = point_to_line_distance(x, y, z)
    elif len(z[2]) == 2:
        centre, radius = find_circle(z[:2], z[2][0], z[2][1])
        distance = point_to_line_distance(x, y, centre) - radius
    elif len(z[2]) == 3:
        distance = line_to_line_distance(z[2][1], z[2][2], x, y)
    else:
        return True
    return distance <= min(bot_dist)


def bisect(z, u, v, centre, radius, x, y):
    chord_midpoint = [(u[0] + v[0]) / 2, (u[1] + v[1]) / 2]
    projection = find_intersection(centre, chord_midpoint, x, y)
    bb = circle_line_segment_intersection(centre, radius, centre, projection, False)
    return bb[0]


def circ_line_relocate(p1, p2, p3, p4, p5):  # p1 is source point, p2 and p3 arc points, p4 and p5 line points
    close_point = closest_point_on_line(p4, p5, p1)
    centre = find_circle(p1, p2, p3)[0]
    p2cart = circ_line_cartesian(p1, close_point, p2, centre)
    p3cart = circ_line_cartesian(p1, close_point, p3, centre)
    p4cart = circ_line_cartesian(p1, close_point, p4, centre)
    p5cart = circ_line_cartesian(p1, close_point, p5, centre)
    line_dist = point_distance(p1, close_point)
    return [[0, 0], p2cart, p3cart, p4cart, p5cart, line_dist]


def circ_derivative(centre, radius, point_on_circle, length_to_line):
    delta = math.radians(get_angle([1, 0], [0, 0], centre))
    theta = math.radians(get_angle([1, 0], [0, 0], point_on_circle))
    return length_to_line * math.sin(theta) / ((math.cos(theta)) ** 2) + 2 * radius * math.sin(theta - delta)


def one_side_bottleneck(z, u, v, x, y, threshold_distance, epsilon):
    centre, radius = find_circle(z, u, v)
    projections = [find_intersection(centre, u, x, y), find_intersection(centre, v, x, y)]
    lengths = [point_distance(u, projections[0]), point_distance(v, projections[1])]
    min_length = min(lengths)
    if lengths.index(min_length) == 0:
        right_bound = v
        left_bound = u
    else:
        right_bound = u
        left_bound = v
    starting_bound = list(left_bound).copy()
    current_bisect = bisect(z, left_bound, right_bound, centre, radius, x, y)
    current_dist = point_distance(current_bisect, find_intersection(z, current_bisect, x, y)) - threshold_distance
    while current_dist < 0 or current_dist > epsilon:
        if current_dist > 0:
            right_bound = current_bisect
        else:
            left_bound = current_bisect
        current_bisect = bisect(z, left_bound, right_bound, centre, radius, x, y)
        current_dist = point_distance(current_bisect,
                                     find_intersection(z, current_bisect, x, y)) - threshold_distance
    print(current_dist)
    return starting_bound, current_bisect


def bottleneck_bound(p1, p2, p3, p4, p5, centre, radius, bound, base_length, epsilon):
    proj1 = find_intersection(p1, p2, p4, p5)
    proj2 = find_intersection(p1, p3, p4, p5)
    current_lower_dist = point_distance(p2, proj1) - bound
    current_upper_dist = point_distance(p3, proj2) - bound
    upper_close = False
    lower_close = False
    if (0 <= current_upper_dist <= epsilon):
        upper_close = True
    if (0 <= current_lower_dist <= epsilon):
        lower_close = True
    if upper_close and lower_close:
        print("TYPE 1", current_upper_dist, current_lower_dist)
        return [p2, p3]
    else:
        current_bisect = bisect(p1, p2, p3, centre, radius, p4, p5)
        current_dist = point_distance(current_bisect, find_intersection(p1, current_bisect, p4, p5))
        if current_dist < bound:
            print("TYPE 2a", current_upper_dist, current_lower_dist)
            new_upper = one_side_bottleneck(p1, current_bisect, p3, p4, p5, bound, epsilon)[1]
            new_lower = one_side_bottleneck(p1, p2, current_bisect, p4, p5, bound, epsilon)[1]
            return [new_upper, new_lower]
        else:
            deriv = circ_derivative(centre, radius, current_bisect, base_length)
            if deriv >= 0:
                print("TYPE 2b", current_upper_dist, current_lower_dist, deriv)
                return bottleneck_bound(p1, p2, current_bisect, p4, p5, centre, radius, bound,
                                        base_length, epsilon)
            else:
                print("TYPE 2c", current_upper_dist, current_lower_dist, deriv)
                return bottleneck_bound(p1, current_bisect, p3, p4, p5, centre, radius, bound,
                                        base_length, epsilon)


def bottle_full(x, y, z, bottleneck, epsilon):
    prelim_check = bottle_ext(x, y, z, bottleneck)
    if len(z[2]) != 2 or not prelim_check:
        return [z[3], z[4]]
    centre, radius = find_circle(z[:2], z[2][0], z[2][1])
    projections = [find_intersection(centre, z[3], x, y), find_intersection(centre, z[4], x, y)]
    lengths = [point_distance(z[3], projections[0]), point_distance(z[4], projections[1])]
    bot_dist = []
    for a in z[6]:
        for b in y[6] + x[6]:
            bot_dist.append(bottleneck[a][b])
    threshold_distance = min(bot_dist)
    min_length = min(lengths)
    max_length = max(lengths)
    if max_length <= threshold_distance:
        return [z[3], z[4]]
    elif min_length < threshold_distance and max_length > threshold_distance:
        return one_side_bottleneck(z, z[3], z[4], x, y, threshold_distance, epsilon)
    else:  #
        close_point = closest_point_on_line(x, y, z)
        line_dist = point_distance(z, close_point)
        new_u, new_v = bottleneck_bound(z, z[3], z[4], x, y, centre, radius, threshold_distance, line_dist, epsilon)
        return find_new_relocate(z, z[3], z[4], x, y, new_u, new_v)


def get_circle_intersections(x0, y0, r0, x1, y1, r1):
    # circle 1: (x0, y0), radius r0
    # circle 2: (x1, y1), radius r1

    d = math.sqrt((x1 - x0) ** 2 + (y1 - y0) ** 2)

    # non-intersecting
    if d > r0 + r1:
        return None
    # One circle within other
    if d < abs(r0 - r1):
        return None
    # coincident circles
    if d == 0 and r0 == r1:
        return None
    else:
        a = (r0 ** 2 - r1 ** 2 + d ** 2) / (2 * d)
        h = math.sqrt(r0 ** 2 - a ** 2)
        x2 = x0 + a * (x1 - x0) / d
        y2 = y0 + a * (y1 - y0) / d
        x3 = x2 + h * (y1 - y0) / d
        y3 = y2 - h * (x1 - x0) / d

        x4 = x2 - h * (y1 - y0) / d
        y4 = y2 + h * (x1 - x0) / d

        return [[x3, y3], [x4, y4]]


def find_new_relocate(z, u, v, x, y, new_u, new_v):
    circ1_radius = point_distance([0, 0], new_u)
    circ2_radius = point_distance([0, 0], new_v)

    big_centre, big_radius = find_circle(z, u, v)

    poss_points1 = get_circle_intersections(big_centre[0], big_centre[1], big_radius, z[0], z[1], circ1_radius)
    poss_points2 = get_circle_intersections(big_centre[0], big_centre[1], big_radius, z[0], z[1], circ2_radius)
    poss_points1.sort(key=lambda item: point_to_line_distance(x, y, item))
    poss_points2.sort(key=lambda item: point_to_line_distance(x, y, item))
    return poss_points1[0], poss_points2[0]


def depth(L):
    if L == []:
        return 0
    else:
        return isinstance(L, list) and max(map(depth, L)) - 1


def melzak_check(point1, point2):  # returns false if Melzak will have an error due to Steiner >120 degrees
    check1 = True
    check2 = True
    if len(point1[2]) == 2:
        a = get_angle(point1[2][0], point2, point1[2][1])
        check1 = not 120 <= a <= 240
    if len(point2[2]) == 2:
        b = get_angle(point2[2][0], point1, point2[2][1])
        check2 = not 120 <= b <= 240
    return check1 and check2


def boundary_constraint(p1, p2, hull_bound):
    return hull_bound.contains(Point(p1)) and hull_bound.contains(Point(p2))


def simple_lune_ext(x, y, z, terms):  # to be fixed if x,y interval is vertical
    if z[3] == z[4] == [-1, -1]:
        return z[3], z[4]
    poss1 = find_intersection(x, y, z, z[
        3])  # note we already know that projections of u and v give us an interval equal to or in xy
    poss2 = find_intersection(x, y, z, z[4])
    dist1 = point_distance(poss1, x)
    dist2 = point_distance(poss2, x)
    if dist1 <= dist2:
        ix = poss1
        iy = poss2
    else:
        ix = poss2
        iy = poss1
    iy, xiy_dist = simple_ext_lemma(x, iy, y, z, terms)
    ix, yix_dist = simple_ext_lemma(y, ix, x, z, terms)
    if point_distance(x, ix) >= xiy_dist:
        return False, False
    else:
        return ProjectionToArc(z, ix), ProjectionToArc(z, iy)


def simple_ext_lemma(x, iy, y, z, terminals):  # horizontal lune test
    xy_gradient = (y[1] - x[1]) / (y[0] - x[0])
    points_in_lune = []
    for point in terminals:
        if lune_constraint(x, iy, point) and point not in [x, y, z]:
            points_in_lune.append(point)
    point_dists = []
    if len(point_dists) > 0:
        for point in points_in_lune:
            angle = get_angle(y, x, point)
            x_dist = point_distance(x, point)
            if 60 <= angle <= 300:
                point_dists.append(x_dist / 2 * math.cos(angle))
                # don't need to worry which side of angle since cos(360 - angle) = cos(angle)
            else:
                point_dists.append(x_dist)
        min_dist = min(point_dists)
        if y[0] >= x[0]:
            new_iy = [x[0] + math.sqrt(min_dist / (1 + xy_gradient ** 2)),
                      x[1] + xy_gradient * math.sqrt(min_dist / (1 + xy_gradient ** 2))]
        else:
            new_iy = [x[0] - math.sqrt(min_dist / (1 + xy_gradient ** 2)),
                      x[1] - xy_gradient * math.sqrt(min_dist / (1 + xy_gradient ** 2))]
    else:
        new_iy = iy
        min_dist = 0
    return new_iy, min_dist


def One_Steiner(n, terminals, times, edge_counts, triple_counts, quad_counts, edge_counter, trip_counter, quad_counter,
               kk, fst_size):
    branch_set = [[] for x in
                  range(kk + 1)]  # general data structure for branches: list with [location,topology,angles]
    branch_set[0].extend(terminals)  # index is size of branch minus 1

    g = Graph(n)
    for i in range(n):
        for j in range(i, n):
            g.add_edge(i, j, point_distance(terminals[i], terminals[j]))

    clean_list = g.kruskal()

    bottleneck = [[0] * n for i in range(n)]
    components = [[x] for x in range(n)]

    ordered_clean_list = sorted(clean_list, key=lambda edge: edge[2])

    for edge in ordered_clean_list:
        for part in components:
            if edge[0] in part:
                comp1 = part
            if edge[1] in part:
                comp2 = part
        for i in comp1:
            for j in comp2:
                bottleneck[i][j] = edge[2]
                bottleneck[j][i] = edge[2]
        newcomp = comp1 + comp2
        components.remove(comp1)
        components.remove(comp2)
        components.append(newcomp)

    fst_set = [[0, point_distance(terminals[i], terminals[j]), [i, j], [terminals[i][:2], terminals[j][:2]]] for
               [i, j, w] in
               clean_list]  # first element of list is number of steiner points, second is length
    part1 = 0
    part2 = 0
    part3 = 0
    part4 = 0

    terminals_short = [tuple(point[:2]) for point in terminals]

    hull = MultiPoint(terminals_short).convex_hull
    hull_boundary = MultiPoint(terminals_short).convex_hull.boundary

    for combo in combinations(terminals, 2):
        part1 += 2

        ep1 = equipoint2(combo[0], combo[1])
        ep2 = equipoint2(combo[1], combo[0])

        if not (boundary_constraint(combo[0], combo[1], hull_boundary) and hull.contains(Point(ep1[:2]))):
            branch_set[1].append(ep1)

        if not (boundary_constraint(combo[0], combo[1], hull_boundary) and hull.contains(Point(ep2[:2]))):
            branch_set[1].append(ep2)
    checking = 0
    for combo in combinations(terminals, 3):
        if not conjecture or (
                (not dist_constraint(combo[0], combo[1], combo[2]) or not dist_constraint(combo[1], combo[0], combo[
                    2])) or not dist_constraint(combo[2], combo[1], combo[0])):
            if not conjecture or ((not reverse_dist(combo[0], combo[1], combo[2]) or not reverse_dist(combo[1], combo[0],
                                                                                                    combo[
                                                                                                        2])) or not reverse_dist(
                combo[2], combo[1], combo[0])):
                polygon = [point[:2] for point in combo]
                xmin, xmax, ymin, ymax = gridrange(polygon)
                polygon_empty = True
                for xx in range(xmin, xmax + 1):
                    for yy in range(ymin, ymax + 1):
                        for j in grid[xx][yy]:
                            if ray_tracing_method(j[0], j[1], polygon) and j not in combo:
                                polygon_empty = False
                                break
                        if not polygon_empty:
                            break
                    if not polygon_empty:
                        break
                if polygon_empty: #to confirm in 10/1/23 meeting
                    pairs = [[combo[0], combo[1]], [combo[0], combo[2]], [combo[1], combo[2]]]
                    pairs.sort(key=lambda item: point_distance(item[0], item[1]))
                    a = pairs[2][0]
                    b = pairs[2][1]
                    other = [point for point in combo if point not in pairs[2]][0]
                    checking += 1
                    if point_to_line_distance(a, b, other) <= min(bottleneck[a[6][0]][other[6][0]],
                                                               bottleneck[b[6][0]][other[6][0]]):
                        if not (boundary_constraint(a, b, hull_boundary) and hull.contains(Point(other[:2]))):
                            branch_set[1].append(equipoint3(other, a, b))
                            part2 += 1

    eff = [0, 0, 0, 0, 0, 0]
    tot = [0, 0, 0, 0, 0, 0]

    for i in range(1, kk + 1):  # Generate the sets of branches and FSTs with $i$ s.p.
        print("i is ", i)
        for m in range(math.floor(i / 2) + 1):  # check range
            print("m is ", m)
            print(i - m, m, len(branch_set[i - m]), len(branch_set[m]))
            for first_branch in branch_set[m]:
                for second_branch in branch_set[i - m]:
                    if not bool(set(first_branch[6]) & set(second_branch[6])):
                        if 1 < i < kk:
                            if DoConesOverlap(first_branch, second_branch):
                                part3 += 1
                                if equipoint2(combo[0], combo[1]) not in branch_set[i + 1]:
                                    branch_set[i + 1].extend(
                                        [equipoint2(combo[0], combo[1]), equipoint2(combo[1], combo[0])])
                        if is_point_in_cone(first_branch, second_branch) and is_point_in_cone(second_branch, first_branch):
                            k_sum = first_branch[5] + second_branch[5]
                            if k_sum == 1:
                                if len(second_branch[
                                           2]) == 2:  # second branch is guaranteed to be the one with non-zero k_sum
                                    a = first_branch[:2]
                                    b = second_branch[2][0][:2]
                                    c = second_branch[2][1][:2]
                                    steiner_point = steiner(a, b, c)
                                    if not bottle_on or bottle_constraint([a, b, c], steiner_point, terminals, bottleneck):
                                        if steiner_point not in [a, b, c]:
                                            if all([terms_in_lune(a, steiner_point, terminals, [a]),
                                                    terms_in_lune(b, steiner_point, terminals, [b]),
                                                    terms_in_lune(c, steiner_point, terminals, [c])]):
                                                fst_set.append([1, point_distance(a, steiner_point) + point_distance(b,
                                                                                                                   steiner_point) + point_distance(
                                                    c, steiner_point), first_branch[6] + second_branch[6],
                                                                [[a, steiner_point], [b, steiner_point],
                                                                 [c, steiner_point]]])
                                else:
                                    a = second_branch[2][0][:2]
                                    b = first_branch[:2]
                                    c = second_branch[2][1][:2]
                                    d = second_branch[2][2][:2]
                                    cross_point = find_intersection(a, b, c, d)
                                    cross_point_in_ab = (a[0] <= cross_point[0] <= b[0]) or (
                                                b[0] <= cross_point[0] <= a[0])
                                    cross_point_in_cd = (c[0] <= cross_point[0] <= d[0]) or (
                                                d[0] <= cross_point[0] <= c[0])
                                    if cross_point_in_ab and cross_point_in_cd:
                                        if bottle_constraint([a, b, c, d], cross_point, terminals, bottleneck):
                                            if vertical_constraint(a, b, c, d) and vertical_constraint(c, d, a, b):
                                                if ((is_point_in_cone(second_branch, first_branch) and (not conjecture or not dist_constraint(
                                                        c, d,
                                                        b))) and (not conjecture or not reverse_dist(
                                                    c, d, b))) and lune_constraint(c, d,
                                                                                 b):  # if the point is in the cone, lune and distance constraints
                                                    if ((quad_constraint(a, b, c) and quad_constraint(a, b,
                                                                                                    d)) and quad_constraint(
                                                            c,
                                                            d,
                                                            a)) and quad_constraint(
                                                        c, d, b):
                                                        if cross_point not in [a, b, c, d]:
                                                            if all([terms_in_lune(a, cross_point, terminals, [a]),
                                                                    terms_in_lune(b, cross_point, terminals, [b]),
                                                                    terms_in_lune(c, cross_point, terminals, [c]),
                                                                    terms_in_lune(d, cross_point, terminals, [d])]):
                                                                fst_set.append(
                                                                    [1, point_distance(a, b) + point_distance(c, d),
                                                                     first_branch[6] + second_branch[6],
                                                                     [[b, cross_point], [a, cross_point],
                                                                      [c, cross_point],
                                                                      [d, cross_point]]])
                            else:
                                new_fst = reverse_melzak(first_branch, second_branch)
                                if not any(edge is False for edge in new_fst):
                                    edge_dists = [point_distance(edge[0], edge[1]) for edge in new_fst]
                                    if not any(dist == 0 for dist in edge_dists):

                                        lunes_empty = True
                                        for edge in new_fst:
                                            if not terms_in_lune(edge[0], edge[1], terminals, [edge[0], edge[1]]):
                                                lunes_empty = False
                                                break
                                            if not lunes_empty:
                                                break
                                        if lunes_empty:
                                            distance_sum = sum(edge_dists)
                                            hyperedge = first_branch[6] + second_branch[6]
                                            fst_set.append([k_sum, distance_sum, hyperedge, new_fst])
            if m <= math.ceil(i / 3) and i < kk:
                for q in range(m, max(math.floor((i - m) / 2), 1)):
                    print(m, q, i - (m + q))
                    print("Checking ", len(branch_set[m]) * len(branch_set[q]) * len(branch_set[i - (m + q)]))
                    for first_branch in branch_set[m]:
                        for second_branch in branch_set[q]:
                            for third_branch in branch_set[i - (m + q)]:
                                if len(set([(branch[0], branch[1]) for branch in
                                            [first_branch, second_branch, third_branch]])) == 3:
                                    if (not bool(set(first_branch[6]) & set(second_branch[6])) and not bool(
                                            set(first_branch[6]) & set(third_branch[6]))) and not bool(
                                            set(third_branch[6]) & set(second_branch[6])):
                                        bordercase = True
                                        if m == q == 0:
                                            if boundary_constraint(first_branch[:2], second_branch[:2],
                                                                  hull_boundary) and hull.contains(
                                                    Point(third_branch[:2])):
                                                bordercase = False
                                        if bordercase:
                                            choices = [first_branch, second_branch, third_branch]
                                            for choice in choices:
                                                # if len(choice[2]) > 0:
                                                #     print("MAYBE")
                                                rest = [x for x in choices if x != choice]
                                                if is_point_in_cone(rest[0], rest[1]) and is_point_in_cone(rest[1], rest[0]):
                                                    NPx, NPy = NonPseudoPair(rest[0], rest[1])
                                                    # if NPx[:2] not in [choice[:2],choice[3][:2],choice[4][:2]] and NPy[:2] not in [choice[:2],choice[3][:2],choice[4][:2]]:
                                                    new_choice = choice.copy()
                                                    new_choice[3], new_choice[4] = IntervalProjectionTest(new_choice,
                                                                                                          NPx, NPy)
                                                    if new_choice[
                                                        3] != False:  # can make new_params once I add the bit where we project back onto the arc
                                                        new_choice[3], new_choice[4] = simple_lune_ext(NPx, NPy,
                                                                                                       new_choice,
                                                                                                       terminals)
                                                        if not bottle_on or new_choice[3] != False:
                                                            new_choice[3], new_choice[4] = bottle_full(NPx, NPy,
                                                                                                       new_choice,
                                                                                                       bottleneck, 0.01)
                                                            if (not rhombus_on or rhombus_ext(new_choice, NPx,
                                                                                              NPy)) and (
                                                                    not conjecture or alpha_ext(new_choice[3],
                                                                                                new_choice[4], NPx,
                                                                                                NPy)) and (
                                                                    not triangle_on or triangle_ext(new_choice, NPx,
                                                                                                    NPy, grid)):
                                                                part4 += 1
                                                                branch_set[i + 1].append(
                                                                    equipoint3(new_choice, rest[0], rest[1]))

    for FST in fst_set:
        FST[2].sort()

    d = {}  # removing fst's if there exists an fst on the same terminals with same or smaller length.
    for sub in fst_set:
        print()
        k = tuple([sub[0],tuple(sub[2])])
        if k not in d or sub[1] < d[k][1]:
            d[k] = sub

    fst_set = list(d.values())
    print("We ended up with ", len(fst_set), " FST's.")

    jae_set = [[i[0] for i in fst_set], [i[1] for i in fst_set], [i[2] for i in fst_set], [i[3] for i in fst_set]]
    jae_counts = [len(x) for x in jae_set]
    timestr = time.strftime("%Y%m%d-%H%M%S")

    output = [test_inputs[0], [point[:2] for point in terminals]]
    output.extend(jae_set)
    output.extend(jae_counts)
    with open('steineroutput%s.txt' % timestr, 'w+') as file:
        file.writelines([str(line) + "\n" for line in output])

    num_edges = sum(1 for x in fst_set if len(x[2]) == 2)
    num_3steiner = sum(1 for x in fst_set if len(x[2]) == 3)
    num_4steiner = sum(1 for x in fst_set if len(x[2]) == 4)

    edge_counter += num_edges
    trip_counter += num_3steiner
    quad_counter += num_4steiner

    return terminals, jae_set, times, edge_counts, triple_counts, quad_counts


while True:
    try:
        rand_check = input("Random points (R), given points (G), or grid-like points (GL)? ")
        if rand_check == "R" or rand_check == "G" or rand_check == "GL":
            print("Entered successfully!")
            break
        else:
            print("I did not understand your input.")
    except:
        continue

while True:
    try:
        kk = int(input("What is k? "))
        if kk >= 0:
            print("Entered successfully! ")
            break
        else:
            print("k should be non-negative")
    except ValueError:
        print("Provide a non-negative integer value...")
        continue

if rand_check == "R" or rand_check == "GL":
    aa = int(input("Start of range? "))
    bb = int(input("End of range? "))
    if bb - aa > 0:
        cc = int(input("What is the step size? "))
    else:
        cc = 1
    r = int(input("Number of repeats? "))
    test_inputs = range(aa, bb+cc,cc)
    if rand_check == "GL":
        perturb = float(input("How big a perturbation (0.0-1.0)? "))
elif rand_check == "G":
    filename = input("What is the filename (including extension)? ")

    with open(filename, 'r') as file:
        fileinfo = file.read().splitlines()
    points = ast.literal_eval(fileinfo[0])

    test_inputs = [len(points)]
    r = 1

ave_times = []
ave_fst_num = []
ave_fst_size = []
ave_steiner_num = []
ave_deg4_num = []

edge_counts = []
triple_counts = []
quad_counts = []

bottle_on = True
rhombus_on = True
triangle_on = True
conjecture = False

plotting = True
concat = True

edge_counter = 0
trip_counter = 0
quad_counter = 0

ff = 5  # ff and gg determine grid size when allocating points
gg = 5

# while quad_counter < 1:
for n in test_inputs:
    times = []
    fst_num = []
    fst_size = []
    steiner_num = []
    deg4_num = []
    for i in range(r):
        print("Now checking ", n, " terminals, ",i+1, " of ", r, "repeats.")
        start_time = time.time()
        if rand_check == "G":
            terminals = [x + [[], [-1, -1], [-1, -1], 0, [points.index(x)]] for x in points]
            print(terminals)
        elif rand_check == "R":
            terminals = []
            for q in range(n):  # randomly generates points, of form (x,y,topology,points at ends of arc,line/arc flag)
                newpoint = [random.random(), random.random(), [], [-1, -1], [-1, -1], 0, [q]]
                terminals.append(newpoint)
        else:
            if math.floor(math.sqrt(n)) ** 2 == n:
                qq = int(math.sqrt(n))
                rr = int(math.sqrt(n))
            else:
                root = math.sqrt(n)
                qq = int(math.floor(root)) + 1
                rr = qq

            points = []
            count = 0
            for ii in range(qq):
                for jj in range(rr):
                    count += 1
                    point = [jj / (qq - 1), ii / (rr - 1)]
                    for xx in range(2):
                        if point[xx] < perturb:
                            point[xx] = point[xx] + random.uniform(-point[xx], perturb)
                        elif point[xx] > 1 - perturb:
                            point[xx] = point[xx] + random.uniform(-perturb, 1 - point[xx])
                        else:
                            point[xx] = point[xx] + random.uniform(-perturb, perturb)
                    points.append(point)
                    if count == n:
                        break
                else:
                    continue
                break
            terminals = [x + [[], [-1, -1], [-1, -1], 0, [points.index(x)]] for x in points]
        grid = [[[] for x in range(gg)] for y in range(ff)]

        for point in terminals:
            gridx, gridy = gridloc(point)
            point.append([gridx, gridy])
            grid[gridx][gridy].append(point)

        terminals, jae_set, times, edge_counts, triple_counts, quad_counts = One_Steiner(n, terminals, times,
                                                                                        edge_counts, triple_counts,
                                                                                        quad_counts, edge_counter,
                                                                                        trip_counter, quad_counter, kk,
                                                                                        fst_num)

        if (r == 1 and len(test_inputs) == 1) and concat == False:

            fig, ax = plt.subplots()

            xs = [point[0] for point in terminals]  # this part is for plotting the points
            ys = [point[1] for point in terminals]
            plt.scatter(xs, ys)

            for i in range(len(terminals)):
                ax.annotate(i, (xs[i], ys[i]))

            for tops in jae_set[3]:
                if len(tops) == 2:
                    x = [tops[0][0], tops[1][0]]
                    y = [tops[0][1], tops[1][1]]
                    plt.plot(x, y, 'r')
                else:
                    for edge in tops:
                        x = [edge[0][0], edge[1][0]]
                        y = [edge[0][1], edge[1][1]]
                        if len(tops) == 3:
                            plt.plot(x, y, 'b')
                        else:
                            plt.plot(x, y, 'k')

            ax.set_xlim([0, 1])
            ax.set_ylim([0, 1])
            ax.set_aspect('equal')
            plt.show()

        if concat == True:
            fst_num.append(len(jae_set[0]))
            fst_size.append(sum([len(x) for x in jae_set[2]]) / len(jae_set[2]))
            n = int(n)
            # number of Steiner points in each hyperedge
            S = jae_set[0]
            # length of each hyperedge
            L = jae_set[1]
            # terminals in each hyperedge
            T = jae_set[2]
            # list of edges
            topologies = jae_set[3]
            # number of iterations
            iter = 1
            # number of cut-constraints implemented
            cutno = 0

            milp_model = gp.Model("milp")
            milp_model.Params.LogToConsole = 0

            # number of hyperedges
            h = len(S)
            print(h)

            x = milp_model.addVars(h, vtype=GRB.BINARY)

            milp_model.setObjective(sum(L[i] * x[i] for i in range(h)), GRB.MINIMIZE)
            c2 = milp_model.addConstr(sum(S[i] * x[i] for i in range(h)) <= kk)

            milp_model.optimize()

            xvalues = np.zeros((h), dtype=int)
            for i in range(h):
                xvalues[i] = x[i].x

            print("Number of iterations is " + str(iter))
            print("Number of cut-constraints implemented is " + str(cutno) + " out of a possible " + str(2**(n-1)-1))
            components = [i for i in range(n)]

            hypertree = find(xvalues, 1)
            for i in range(len(hypertree)):
                currenthyper = hypertree[i]
                vincurrenthyper = T[currenthyper]

                comps = [components[i] for i in vincurrenthyper]
                aa = len(comps)
                compsnodouble = list(set(comps))
                ab = len(compsnodouble)

                nextitcomp = np.min(compsnodouble)

                for j in range(ab):
                    if nextitcomp != compsnodouble[j]:
                        tempind = find(components, compsnodouble[j])
                        for k in tempind:
                            components[k] = nextitcomp

            # number of comps in the current graph
            noofcomps = len(list(set(components)))

            print(components)

            while noofcomps > 1.5:

                if noofcomps == 2:
                    # labels of different components
                    dfjeqns = np.zeros((1, h), dtype=int)
                    cutno = cutno + 1

                    for i in range(h):
                        currenth = T[i]

                        # currentcompv denotes all vertices in the current component
                        currentcompv = find(components, 0)
                        # notcurrentcompv denotes all vertices not in the current component
                        notcurrentcompv = list(set(range(n)) - set(currentcompv))

                        if len(set(currentcompv) - set(currenth)) < len(currentcompv) and \
                                len(set(notcurrentcompv) - set(currenth)) < len(notcurrentcompv):
                            dfjeqns[0, i] = 1

                    milp_model.addConstr(sum(x[i] * dfjeqns[0, i] for i in range(h)) >= 1)

                elif noofcomps >= 3:
                    # labels of different components
                    l = list(set(components))
                    p = len(l)
                    dfjeqns = np.zeros((p, h), dtype=int)
                    cutno = cutno + noofcomps

                    for i in range(h):
                        currenth = T[i]

                        for j in range(p):
                            # currentcompv denotes all vertices in the current component
                            currentcompv = find(components, l[j])
                            # notcurrentcompv denotes all vertices not in the current component
                            notcurrentcompv = list(set(range(n)) - set(currentcompv))

                            if len(set(currentcompv) - set(currenth)) < len(currentcompv) and \
                                    len(set(notcurrentcompv) - set(currenth)) < len(notcurrentcompv):
                                dfjeqns[j, i] = 1

                    milp_model.addConstrs(sum(x[i] * dfjeqns[j, i] for i in range(h)) >= 1 for j in range(p))

                iter = iter + 1
                milp_model.optimize()

                xvalues = np.zeros((h), dtype=int)
                for i in range(h):
                    xvalues[i] = x[i].x

                print("Number of iterations is " + str(iter))
                print("Number of cut-constraints implemented is " + str(cutno) + " out of a possible " + str(2**(n-1)-1))
                components = [i for i in range(n)]


                hypertree = find(xvalues, 1)
                for i in range(len(hypertree)):
                    currenthyper = hypertree[i]
                    vincurrenthyper = T[currenthyper]

                    comps = [components[i] for i in vincurrenthyper]
                    aa = len(comps)
                    compsnodouble = list(set(comps))
                    ab = len(compsnodouble)

                    nextitcomp = np.min(compsnodouble)

                    for j in range(ab):
                        if nextitcomp != compsnodouble[j]:
                            tempind = find(components, compsnodouble[j])
                            for k in tempind:
                                components[k] = nextitcomp

                # number of comps in the current graph
                noofcomps = len(list(set(components)))

            htree = find(xvalues, 1)

            def count(l):
                return sum(1 + count(i) for i in l if isinstance(i, list))


            # number of degree 4 steiner points in fst is t - 2 -s where t = # terminals, s = # steiner points

            steiner_num.append(sum(S[x] for x in htree))
            deg4_num.append(sum(len(T[x]) - 2 - S[x] for x in htree))

            print("--- %s seconds ---" % (time.time() - start_time))
            times.append(time.time() - start_time)


            if (plotting == True and r == 1) and len(test_inputs) == 1:
                fig, ax = plt.subplots()

                xs = [point[0] for point in terminals]  # this part is for plotting the points
                ys = [point[1] for point in terminals]

                for i in range(len(terminals)):
                    ax.annotate(i, (xs[i], ys[i]))

                for i in range(len(htree)):
                    a = htree[i]
                    he = topologies[a]
                    c = count(he)
                    if c == 2:
                        plt.plot([he[0][0], he[1][0]], [he[0][1], he[1][1]], 'r')
                    else:
                        for j in range(len(he)):
                            e = he[j]
                            plt.plot([e[0][0], e[1][0]], [e[0][1], e[1][1]], 'b')

                plt.xlim([-0.05, 1.05])
                plt.ylim([-0.05, 1.05])
                ax.set_aspect('equal')

                for i in range(n):
                    plt.scatter(terminals[i][0], terminals[i][1], c='k')
                plt.show()
    print(times)
    ave_times.append(sum(times) / len(times))
    ave_fst_num.append(sum(fst_num) / len(fst_num))
    ave_fst_size.append(sum(fst_size) / len(fst_size))
    ave_steiner_num.append(sum(steiner_num) / len(steiner_num))
    ave_deg4_num.append(sum(deg4_num) / len(deg4_num))
    print(ave_times)
    print(ave_fst_num)
    print(ave_fst_size)
    print(ave_steiner_num)
    print(ave_deg4_num)


if r >= 1 and len(test_inputs) > 1:
    full_results = [ave_times, ave_fst_num, ave_fst_size, ave_steiner_num, ave_deg4_num]

    timestr = time.strftime("%Y%m%d-%H%M%S")
    with open('%s_graphsteiner%s_%s_%s.txt' % (rand_check,test_inputs[0], test_inputs[-1], timestr), 'w+') as file:
        file.writelines([str(line) + "\n" for line in full_results])

    w = test_inputs
    x = ave_times
    plt.plot(w, x, label="# of edges")
    plt.xlabel('# of terminals')
    plt.ylabel('Times')
    plt.show()

    x = test_inputs
    y = ave_fst_num
    plt.plot(x, y)
    plt.xlabel('# of terminals')
    plt.ylabel('Number of FST\'s')
    plt.show()

    x = ave_deg4_num
    plt.plot(w, x, label="# of edges")
    plt.xlabel('# of terminals')
    plt.ylabel('# of degree-4 vertices')
    plt.show()

    x = ave_fst_size
    plt.plot(w, x, label="# of edges")
    plt.xlabel('# of terminals')
    plt.ylabel('Average size of FST\'s')
    plt.show()

    x = ave_steiner_num
    plt.plot(w, x, label="# of edges")
    plt.xlabel('# of terminals')
    plt.ylabel('Average # of Steiner points')
    plt.show()
    ###########################################################################
